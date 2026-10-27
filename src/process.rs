//! Interruptible compiler subprocesses. Signal handlers only publish a number;
//! normal control flow forwards it, reaps children, and unwinds resource guards.
use nix::sys::signal::{Signal, killpg};
use nix::unistd::Pid;
use signal_hook::consts::{SIGINT, SIGTERM};
use std::io::{self, Read, Write};
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

pub(crate) fn capture(mut command: Command, input: Option<&[u8]>) -> io::Result<Output> {
    check()?;
    let mut child = command
        .process_group(0)
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let group = Pid::from_raw(child.id() as i32);
    let stdout = child.stdout.take().expect("piped stdout");
    let stderr = child.stderr.take().expect("piped stderr");
    let read = |mut pipe: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            pipe.read_to_end(&mut bytes).map(|_| bytes)
        })
    };
    let stdout = read(Box::new(stdout));
    let stderr = read(Box::new(stderr));
    let writer = input.map(|input| {
        let bytes = input.to_vec();
        let mut stdin = child.stdin.take().expect("piped stdin");
        std::thread::spawn(move || stdin.write_all(&bytes))
    });
    let mut status = None;
    let mut interrupted = None;
    let mut killed = false;
    let wait_result = (|| {
        loop {
            let signal = received();
            if signal != 0 && interrupted.is_none() {
                let signal = Signal::try_from(signal as i32).unwrap_or(Signal::SIGTERM);
                let _ = killpg(group, signal);
                interrupted = Some(Instant::now());
            }
            if !killed && interrupted.is_some_and(|start| start.elapsed() >= Duration::from_secs(5))
            {
                let _ = killpg(group, Signal::SIGKILL);
                killed = true;
            }
            if status.is_none() {
                status = child.try_wait()?;
            }
            // Descendants can close their inherited pipes while continuing to
            // run. On cancellation, give the whole group the grace period and
            // enforce SIGKILL even when the direct child and I/O already ended.
            if status.is_some()
                && stdout.is_finished()
                && stderr.is_finished()
                && writer.as_ref().is_none_or(|writer| writer.is_finished())
                && (interrupted.is_none() || killed || killpg(group, None).is_err())
            {
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        Ok::<_, io::Error>(())
    })();
    if wait_result.is_err() {
        let _ = killpg(group, Signal::SIGKILL);
        let _ = child.wait();
    }
    let join_error = || io::Error::other("compiler subprocess I/O thread failed");
    let stdout = stdout.join().map_err(|_| join_error())?;
    let stderr = stderr.join().map_err(|_| join_error())?;
    let written = writer
        .map(|writer| writer.join().map_err(|_| join_error()))
        .transpose()?;
    wait_result?;
    check()?;
    // A rejecting backend may close stdin early; preserve its diagnostic output.
    if let Some(Err(error)) = written
        && error.kind() != io::ErrorKind::BrokenPipe
    {
        return Err(error);
    }
    Ok(Output {
        status: status.expect("child reaped"),
        stdout: stdout?,
        stderr: stderr?,
    })
}
