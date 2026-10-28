//! Interruptible compiler subprocesses. Signal handlers only publish a number;
//! normal control flow forwards it, reaps children, and unwinds resource guards.
use nix::fcntl::{FcntlArg, OFlag, fcntl};
use nix::sys::signal::{Signal, killpg};
use nix::unistd::Pid;
use signal_hook::consts::{SIGINT, SIGTERM};
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

static SIGNAL: OnceLock<Arc<AtomicUsize>> = OnceLock::new();

pub(crate) fn install() -> io::Result<()> {
    if SIGNAL.get().is_none() {
        let signal = Arc::new(AtomicUsize::new(0));
        for number in [SIGINT, SIGTERM] {
            signal_hook::flag::register_usize(number, signal.clone(), number as usize)?;
        }
        let _ = SIGNAL.set(signal);
    }
    Ok(())
}

fn received() -> usize {
    SIGNAL
        .get()
        .map_or(0, |signal| signal.load(Ordering::Relaxed))
}

pub(crate) fn exit_code() -> i32 {
    match received() {
        0 => 1,
        signal => 128 + signal as i32,
    }
}

pub(crate) fn check() -> io::Result<()> {
    if received() == 0 {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::Interrupted,
            "compilation interrupted",
        ))
    }
}

#[derive(Debug)]
pub(crate) enum CaptureError {
    Interrupted,
    Spawn(io::Error),
    Wait(io::Error),
    Io(io::Error),
}

// Only post-exit cleanup and cancellation have deadlines. A live compiler has
// no wall-clock limit. All pipe operations are nonblocking, including stdin.
const DRAIN_GRACE: Duration = Duration::from_millis(250);
const TERM_GRACE: Duration = Duration::from_secs(1);
const KILL_GRACE: Duration = Duration::from_secs(1);

fn nonblocking(pipe: &impl AsRawFd) -> io::Result<()> {
    let flags = OFlag::from_bits_truncate(fcntl(pipe.as_raw_fd(), FcntlArg::F_GETFL)?);
    fcntl(
        pipe.as_raw_fd(),
        FcntlArg::F_SETFL(flags | OFlag::O_NONBLOCK),
    )?;
    Ok(())
}

fn drain<P: Read>(pipe: &mut Option<P>, bytes: &mut Vec<u8>) -> io::Result<()> {
    let Some(reader) = pipe else { return Ok(()) };
    // Bound work per iteration so a continuously writing descendant cannot
    // starve signal handling or cleanup deadlines.
    let mut buffer = [0; 8192];
    for _ in 0..8 {
        match reader.read(&mut buffer) {
            Ok(0) => {
                *pipe = None;
                break;
            }
            Ok(count) => bytes.extend_from_slice(&buffer[..count]),
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

pub(crate) fn capture(mut command: Command, input: Option<&[u8]>) -> Result<Output, CaptureError> {
    check().map_err(|_| CaptureError::Interrupted)?;
    let mut child = command
        .process_group(0)
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(CaptureError::Spawn)?;
    let group = Pid::from_raw(child.id() as i32);
    let result = (|| {
        let mut stdout = child.stdout.take();
        let mut stderr = child.stderr.take();
        let mut stdin = child.stdin.take();
        nonblocking(stdout.as_ref().expect("piped stdout")).map_err(CaptureError::Io)?;
        nonblocking(stderr.as_ref().expect("piped stderr")).map_err(CaptureError::Io)?;
        if let Some(pipe) = &stdin {
            nonblocking(pipe).map_err(CaptureError::Io)?;
        }
        let input = input.unwrap_or_default();
        let mut written = 0;
        let mut output = Vec::new();
        let mut errors = Vec::new();
        let mut status = None;
        let mut exited = None;
        let mut terminating = None;
        let mut killed = None;
        let mut forced = false;
        loop {
            let now = Instant::now();
            if terminating.is_none() && received() != 0 {
                let signal = Signal::try_from(received() as i32).unwrap_or(Signal::SIGTERM);
                let _ = killpg(group, signal);
                terminating = Some(now);
            }
            if status.is_none() {
                status = child.try_wait().map_err(CaptureError::Wait)?;
                if status.is_some() {
                    exited = Some(now);
                }
            }
            drain(&mut stdout, &mut output).map_err(CaptureError::Io)?;
            drain(&mut stderr, &mut errors).map_err(CaptureError::Io)?;
            if let Some(pipe) = &mut stdin {
                if written < input.len() {
                    let end = input.len().min(written + 65536);
                    match pipe.write(&input[written..end]) {
                        Ok(count) => written += count,
                        Err(error) if error.kind() == io::ErrorKind::BrokenPipe => {
                            written = input.len()
                        }
                        Err(error)
                            if matches!(
                                error.kind(),
                                io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                            ) => {}
                        Err(error) => return Err(CaptureError::Io(error)),
                    }
                }
                if written == input.len() {
                    stdin = None;
                }
            }
            let group_alive = killpg(group, None).is_ok();
            let io_done = stdout.is_none() && stderr.is_none() && stdin.is_none();
            if status.is_some() && io_done && (!group_alive || killed.is_some()) {
                break;
            }
            if terminating.is_none()
                && exited.is_some_and(|start| now.duration_since(start) >= DRAIN_GRACE)
            {
                forced = true;
                let _ = killpg(group, Signal::SIGTERM);
                terminating = Some(now);
            }
            if killed.is_none()
                && terminating.is_some_and(|start| now.duration_since(start) >= TERM_GRACE)
            {
                let _ = killpg(group, Signal::SIGKILL);
                killed = Some(now);
            }
            if killed.is_some_and(|start| now.duration_since(start) >= KILL_GRACE) {
                // Dropping our pipe ends also bounds escaped descendants that
                // changed process groups while keeping inherited descriptors.
                forced = true;
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        check().map_err(|_| CaptureError::Interrupted)?;
        if forced {
            return Err(CaptureError::Io(io::Error::other(
                "subprocess exited with surviving descendants or open pipes; forced cleanup was required",
            )));
        }
        Ok(Output {
            status: status.expect("child reaped"),
            stdout: output,
            stderr: errors,
        })
    })();
    if result.is_err() {
        let _ = killpg(group, Signal::SIGKILL);
        // Reap the direct child without an unbounded wait, including I/O/setup
        // errors. No reader or writer threads remain to join.
        let deadline = Instant::now() + KILL_GRACE;
        while matches!(child.try_wait(), Ok(None)) && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
    }
    result
}
