//! Interruptible compiler subprocesses. Signal handlers only publish a number;
//! normal control flow forwards it, reaps children, and unwinds resource guards.
use nix::errno::Errno;
use nix::fcntl::{FcntlArg, OFlag, fcntl};
use nix::sys::signal::{Signal, killpg};
use nix::unistd::Pid;
use signal_hook::consts::{SIGHUP, SIGINT, SIGQUIT, SIGTERM};
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
        for number in [SIGINT, SIGTERM, SIGHUP, SIGQUIT] {
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
    /// Standard output exceeded a `Retention::Complete` limit (in bytes).
    OutputLimit(usize),
}

/// How much of a child's output stream the driver keeps in memory.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Retention {
    /// The caller needs every byte (for example a JSON response). Exceeding the
    /// limit stops the child and fails the capture.
    Complete(usize),
    /// Only diagnostics are needed: keep the last bytes and count the rest.
    Tail(usize),
}

/// Diagnostic streams retain at most this many trailing bytes.
pub(crate) const DIAGNOSTIC_TAIL: usize = 1024 * 1024;

struct Sink {
    bytes: Vec<u8>,
    retention: Retention,
    omitted: u64,
    received: u64,
}

impl Sink {
    fn new(retention: Retention) -> Self {
        Self {
            bytes: Vec::new(),
            retention,
            omitted: 0,
            received: 0,
        }
    }

    fn push(&mut self, chunk: &[u8]) -> Result<(), CaptureError> {
        self.received += chunk.len() as u64;
        match self.retention {
            Retention::Complete(limit) => {
                if chunk.len() > limit - self.bytes.len() {
                    return Err(CaptureError::OutputLimit(limit));
                }
                self.bytes.extend_from_slice(chunk);
            }
            Retention::Tail(limit) => {
                self.bytes.extend_from_slice(chunk);
                // Trim in amortized batches; memory stays below twice the tail.
                if self.bytes.len() > 2 * limit {
                    self.trim(limit);
                }
            }
        }
        Ok(())
    }

    fn trim(&mut self, limit: usize) {
        let excess = self.bytes.len().saturating_sub(limit);
        if excess > 0 {
            self.bytes.drain(..excess);
            self.omitted += excess as u64;
        }
    }

    fn finish(mut self) -> Vec<u8> {
        if let Retention::Tail(limit) = self.retention {
            self.trim(limit);
        }
        if self.omitted == 0 {
            return self.bytes;
        }
        let mut bytes = format!("[{} earlier bytes omitted]\n", self.omitted).into_bytes();
        bytes.extend_from_slice(&self.bytes);
        bytes
    }
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

fn drain<P: Read>(pipe: &mut Option<P>, sink: &mut Sink) -> Result<(), CaptureError> {
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
            Ok(count) => sink.push(&buffer[..count])?,
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(CaptureError::Io(error)),
        }
    }
    Ok(())
}

#[cfg(test)]
thread_local! {
    static SENT: std::cell::RefCell<Vec<(Pid, Option<Signal>)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Probe (`None`) or signal the child's process group, unless it is known to be
/// gone. Before the direct child is reaped, its PID reserves the group ID. After
/// it is reaped and the group is observed empty (`ESRCH`), the number may be
/// reused by an unrelated process group, so it is never signaled again.
fn signal_group(group: Pid, signal: Option<Signal>, reaped: bool, gone: &mut bool) -> bool {
    if *gone {
        return false;
    }
    #[cfg(test)]
    SENT.with(|sent| sent.borrow_mut().push((group, signal)));
    match killpg(group, signal) {
        Ok(()) => true,
        Err(Errno::ESRCH) if reaped => {
            *gone = true;
            false
        }
        Err(_) => false,
    }
}

/// Run a compiler subprocess in its own process group. Standard error keeps a
/// bounded tail; `stdout` selects how standard output is retained.
pub(crate) fn capture(
    mut command: Command,
    input: Option<&[u8]>,
    stdout: Retention,
) -> Result<Output, CaptureError> {
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
    let stdout_retention = stdout;
    let mut reaped = false;
    let mut gone = false;
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
        let mut output = Sink::new(stdout_retention);
        let mut errors = Sink::new(Retention::Tail(DIAGNOSTIC_TAIL));
        let mut status = None;
        let mut exited = None;
        let mut terminating = None;
        let mut killed = None;
        let mut forced = false;
        loop {
            let transferred = (written, output.received, errors.received);
            let now = Instant::now();
            if terminating.is_none() && received() != 0 {
                let signal = Signal::try_from(received() as i32).unwrap_or(Signal::SIGTERM);
                signal_group(group, Some(signal), reaped, &mut gone);
                terminating = Some(now);
            }
            if status.is_none() {
                status = child.try_wait().map_err(CaptureError::Wait)?;
                if status.is_some() {
                    reaped = true;
                    exited = Some(now);
                }
            }
            drain(&mut stdout, &mut output)?;
            drain(&mut stderr, &mut errors)?;
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
            let group_alive = signal_group(group, None, reaped, &mut gone);
            let io_done = stdout.is_none() && stderr.is_none() && stdin.is_none();
            if status.is_some() && io_done && (!group_alive || killed.is_some()) {
                break;
            }
            if terminating.is_none()
                && exited.is_some_and(|start| now.duration_since(start) >= DRAIN_GRACE)
            {
                forced = true;
                signal_group(group, Some(Signal::SIGTERM), reaped, &mut gone);
                terminating = Some(now);
            }
            if killed.is_none()
                && terminating.is_some_and(|start| now.duration_since(start) >= TERM_GRACE)
            {
                signal_group(group, Some(Signal::SIGKILL), reaped, &mut gone);
                killed = Some(now);
            }
            if killed.is_some_and(|start| now.duration_since(start) >= KILL_GRACE) {
                // Dropping our pipe ends also bounds escaped descendants that
                // changed process groups while keeping inherited descriptors.
                forced = true;
                break;
            }
            // Keep servicing ready pipes without imposing a per-chunk delay.
            // Each drain/write remains bounded, so signals and deadlines are
            // checked even when a descendant continuously produces output.
            if (written, output.received, errors.received) == transferred {
                std::thread::sleep(Duration::from_millis(10));
            }
        }
        check().map_err(|_| CaptureError::Interrupted)?;
        if forced {
            return Err(CaptureError::Io(io::Error::other(
                "subprocess exited with surviving descendants or open pipes; forced cleanup was required",
            )));
        }
        Ok(Output {
            status: status.expect("child reaped"),
            stdout: output.finish(),
            stderr: errors.finish(),
        })
    })();
    if result.is_err() {
        signal_group(group, Some(Signal::SIGKILL), reaped, &mut gone);
        // Reap the direct child without an unbounded wait, including I/O/setup
        // errors. No reader or writer threads remain to join.
        let deadline = Instant::now() + KILL_GRACE;
        while !reaped && Instant::now() < deadline {
            match child.try_wait() {
                Ok(None) => std::thread::sleep(Duration::from_millis(10)),
                _ => reaped = true,
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capture_preserves_multimegabyte_input_and_output() {
        let bytes = vec![b'x'; 8 * 1024 * 1024];
        let start = Instant::now();
        let output = capture(
            Command::new("cat"),
            Some(&bytes),
            Retention::Complete(bytes.len()),
        )
        .unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, bytes);
        assert!(output.stderr.is_empty());
        eprintln!("8 MiB duplex pipe transfer: {:?}", start.elapsed());
    }

    #[test]
    fn cleanup_never_signals_an_emptied_process_group() {
        // The direct child exits only after a descendant has left its process
        // group (setsid) while keeping the stdout/stderr pipes open. The group ID
        // then reserves nothing, so cleanup must not send SIGTERM/SIGKILL to it.
        let directory = std::env::temp_dir().join(format!(
            "vastitas-process-test-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let marker = directory.join("escaped");
        // The wait for the marker is bounded (#678). If the Python child never
        // writes it, or the directory is gone, the shell gives up after 6000
        // polls, at least 60 s. The test then fails, and a killed run leaves
        // no shell that polls forever.
        let mut command = Command::new("sh");
        command.env("MARKER", &marker).args([
            "-c",
            "python3 -c 'import os, sys, time; os.setsid(); print(os.getpid(), file=open(os.environ[\"MARKER\"] + \".tmp\", \"w\")); os.rename(os.environ[\"MARKER\"] + \".tmp\", os.environ[\"MARKER\"]); time.sleep(4)' &\n\
             polls=0\n\
             while [ ! -f \"$MARKER\" ]; do\n\
             if [ \"$polls\" -ge 6000 ] || [ ! -d \"${MARKER%/*}\" ]; then exit 1; fi\n\
             polls=$((polls + 1))\n\
             sleep 0.01\n\
             done\nexit 0\n",
        ]);
        SENT.with(|sent| sent.borrow_mut().clear());
        let start = Instant::now();
        let error = capture(command, None, Retention::Tail(1024)).unwrap_err();
        let elapsed = start.elapsed();
        let sent = SENT.with(|sent| sent.take());
        if let Ok(pid) = std::fs::read_to_string(&marker) {
            let _ =
                nix::sys::signal::kill(Pid::from_raw(pid.trim().parse().unwrap()), Signal::SIGKILL);
        }
        let _ = std::fs::remove_dir_all(&directory);
        assert!(
            matches!(&error, CaptureError::Io(error) if error.to_string().contains("forced cleanup")),
            "{error:?}"
        );
        assert!(elapsed < Duration::from_secs(4), "{elapsed:?}");
        assert!(!sent.is_empty());
        assert!(
            sent.iter().all(|(_, signal)| signal.is_none()),
            "signals sent to an emptied process group: {sent:?}"
        );
    }

    #[test]
    fn capture_bounds_retained_output() {
        let mut command = Command::new("sh");
        command.args([
            "-c",
            "head -c 3000000 /dev/zero | tr '\\0' a; head -c 3000000 /dev/zero | tr '\\0' b >&2; printf end >&2",
        ]);
        let output = capture(command, None, Retention::Tail(1000)).unwrap();
        assert!(output.status.success());
        assert_eq!(
            output.stdout,
            [
                b"[2999000 earlier bytes omitted]\n".as_slice(),
                &[b'a'; 1000]
            ]
            .concat()
        );
        let omitted = format!("[{} earlier bytes omitted]\n", 3_000_003 - DIAGNOSTIC_TAIL);
        assert!(output.stderr.starts_with(omitted.as_bytes()));
        assert_eq!(output.stderr.len(), omitted.len() + DIAGNOSTIC_TAIL);
        assert!(output.stderr.ends_with(b"bbbend"));

        let mut command = Command::new("sh");
        command.args(["-c", "exec yes"]);
        let start = Instant::now();
        let error = capture(command, None, Retention::Complete(1 << 20)).unwrap_err();
        assert!(matches!(error, CaptureError::OutputLimit(limit) if limit == 1 << 20));
        assert!(start.elapsed() < Duration::from_secs(10));
    }
}
