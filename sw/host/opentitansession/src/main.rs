// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, Result};
use clap::Parser;
use directories::{BaseDirs, ProjectDirs};
use erased_serde::Serialize;
use log::LevelFilter;
use nix::sys::signal::{self, Signal};
use nix::unistd::{dup2, setsid, Pid};
use std::env::{self, args_os, ArgsOs};
use std::ffi::OsString;
use std::fs::{self, read_to_string, File};
use std::io::{self, ErrorKind, Write};
use std::iter::Iterator;
use std::os::unix::io::AsRawFd;
use std::path::PathBuf;
use std::process::{self, ChildStdout, Command, Stdio};
use std::str::FromStr;
use std::time::Duration;

use opentitanlib::proxy::SessionHandler;
use opentitanlib::{backend, util};

#[derive(Debug, Parser)]
#[command(
    name = "opentitansession",
    about = "A tool for interacting with OpenTitan chips."
)]
struct Opts {
    #[arg(
        long,
        value_parser = PathBuf::from_str,
        default_value = "config",
        help = "Filename of a default flagsfile.  Relative to $XDG_CONFIG_HOME/opentitantool."
    )]
    rcfile: PathBuf,

    #[arg(long, default_value = "off")]
    logging: LevelFilter,

    #[command(flatten)]
    backend_opts: backend::BackendOpts,

    #[arg(
        long,
        help = "Stop a running session, optionally combine with --listen_port for disambiguation"
    )]
    stop: bool,

    #[arg(
        long,
        help = "Optional, defaults to 9900 or nearest higher available port."
    )]
    listen_port: Option<u16>,

    #[arg(
        long,
        help = "Start session, staying in foreground (do not daemonize).  Session process will terminate if its parent dies."
    )]
    foreground: bool,

    #[arg(
        long,
        help = "Internal, used to tell the child process to run as a daemon."
    )]
    child: bool,
}

// Given some existing option configuration, maybe re-evaluate command
// line options by reading an `rcfile`.
fn parse_command_line(opts: Opts, mut args: ArgsOs) -> Result<Opts> {
    // Initialize the logger if the user requested the non-defualt option.
    let logging = opts.logging;
    if logging != LevelFilter::Off {
        env_logger::Builder::from_default_env()
            .filter(None, opts.logging)
            .init();
    }
    if opts.rcfile.as_os_str().is_empty() {
        // No rcfile to parse.
        return Ok(opts);
    }

    // Construct the rcfile path based on the user's config directory
    // (ie: $HOME/.config/opentitantool/<filename>).
    let rcfile = if let Some(base) = ProjectDirs::from("org", "opentitan", "opentitantool") {
        base.config_dir().join(&opts.rcfile)
    } else {
        opts.rcfile
    };

    // argument[0] is the executable name.
    let mut arguments = vec![args.next().unwrap()];

    // Read in the rcfile and extend the argument list.
    match read_to_string(&rcfile) {
        Ok(content) => {
            for line in content.split('\n') {
                // Strip basic comments as shellwords won't handle comments.
                let (line, _) = line.split_once('#').unwrap_or((line, ""));
                arguments.extend(shellwords::split(line)?.iter().map(OsString::from));
            }
            Ok(())
        }
        Err(e) if e.kind() == ErrorKind::NotFound => {
            log::warn!("Could not read {:?}. Ignoring.", rcfile);
            Ok(())
        }
        Err(e) => Err(anyhow::Error::new(e).context(format!("Reading file {:?}", rcfile))),
    }?;

    // Extend the argument list with all remaining command line arguments.
    arguments.extend(args);
    let opts = Opts::parse_from(&arguments);
    if opts.logging != logging {
        // Try re-initializing the logger.  Ignore errors.
        let _ = env_logger::Builder::from_default_env()
            .filter(None, opts.logging)
            .try_init();
    }
    Ok(opts)
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct SessionStartResult {
    port: u16,
}

/// Spawn a child process, passing all the same arguments to the child, letting it instantiate a
/// Transport based on the command line arguments, listen on a TCP socket, and run as a daemon
/// process serving network requests.  Success of the child is verified by means of a
/// `SessionStartResult` JSON message sent through the standard output pipe.
fn start_session(run_file_fn: impl FnOnce(u16) -> PathBuf) -> Result<Box<dyn Serialize>> {
    let mut child = Command::new(env::current_exe()?) // Same executable
        .arg("--child") // Add argument to let the new process know it is the daemon child
        .args(args_os().skip(1)) // Propagate all existing arguments: --interface, etc.
        .stdin(Stdio::null()) // Not used by child, disconnect from terminal
        .stdout(Stdio::piped()) // Used for signalling completion of daemon startup
        .stderr(Stdio::inherit()) // May be used for error messages during daemon startup
        .spawn()?;

    match serde_json::from_reader::<&mut ChildStdout, Result<SessionStartResult, String>>(
        child.stdout.as_mut().unwrap(),
    ) {
        Ok(Ok(result)) => {
            // Create a pid file corresponding to the requested TCP port.
            let path = run_file_fn(result.port);
            File::create(path)?.write_all(format!("{}\n", child.id()).as_bytes())?;
            Ok(Box::new(result))
        }
        Ok(Err(e)) => bail!(e),
        Err(e) => bail!("Child process failed to start: {}", e),
    }
}

// This method runs in the daemon child.  It will instantiate SessionHandler to bind to a
// socket, then report the chosen port number to the parent process by means of a serialized
// `SessionStartResult` sent through the stdout anonymous pipe, and finally enter an infnite
// loop, processing connections on that socket
fn session_child(listen_port: Option<u16>, backend_opts: &backend::BackendOpts) -> Result<()> {
    let transport = backend::create(backend_opts)?;
    let mut session = SessionHandler::init(&transport, listen_port)?;
    // Instantiation of Transport backend, and binding to a socket was successful, now go
    // through the process of making this process a daemon, disconnected from the
    // terminal that was used to start it.

    // All configuration files have been processed (relative to current direction), we can now
    // drop the reference to the file system, (in case the admin wants to unmount while this
    // daemon is still running.)
    env::set_current_dir("/")?;

    // Close stderr, which remained open in order to allow any errors from the above code to
    // surface, but needs to be severed in order for the daemon to avoid being killed by SIGHUP
    // if the user closes the terminal window.
    dup2(File::open("/dev/null")?.as_raw_fd(), 2)?;

    // After severing the only connection to the controlling terminal inherited from the parent,
    // we can now establish a new Unix "session" for this process, which will not be
    // "controlled" by any terminal.  This means that this daemon will not be killed by SIGHUP,
    // in case the terminal that was used for running `session start` is later closed.
    setsid()?;

    // Report startup success to parent process.
    serde_json::to_writer::<io::Stdout, Result<SessionStartResult, String>>(
        io::stdout(),
        &Ok(SessionStartResult {
            port: session.get_port(),
        }),
    )?;
    io::stdout().flush()?;

    // Closing the standard output pipe is the signal to the parent process that this child has
    // started up successfully.  We close the pipe indirectly, by replacing file descriptor 1
    // with one pointing to /dev/null.  This will ensure that any subsequent accidentally
    // executed println!() will be a no-op, rather than trigger termination via SIGPIPE.
    dup2(2, 1)?;

    // Indefinitely run command processing loop in this daemon process.
    session.run_loop()
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct SessionStopResult {}

/// Load .pid file based on given port number, and send SIGTERM to the process identified in the
/// file, to request the daemon gracefully shut down.
fn stop_session(run_file_fn: impl FnOnce(u16) -> PathBuf, port: u16) -> Result<Box<dyn Serialize>> {
    // Read the pid file corresponding to the requested TCP port.
    let path = run_file_fn(port);
    let pid: i32 = FromStr::from_str(fs::read_to_string(&path)?.trim())?;
    // Send signal to daemon process, asking it to terminate.
    signal::kill(Pid::from_raw(pid), Signal::SIGTERM)?;
    // Wait for daemon process to stop.
    loop {
        std::thread::sleep(Duration::from_millis(100));
        // Send "signal 0", meaning that the kernel performs error checks (among those, checking
        // that the target process exists), without actually sending any signal.
        match signal::kill(Pid::from_raw(pid), None) {
            Ok(()) => (), // Process still running, repeat.
            Err(nix::errno::Errno::ESRCH) => {
                // Process could not be found, meaning that it has terminated, as expected.
                fs::remove_file(&path)?;
                return Ok(Box::new(SessionStopResult {}));
            }
            Err(e) => bail!("Unexpected error querying process presence: {}", e),
        }
    }
}

fn main() -> Result<()> {
    let opts = parse_command_line(Opts::parse(), args_os())?;

    if opts.foreground {
        // Start session process in foreground (do not daemonize).  The session process will
        // terminate if its parent dies.  This might be useful for use in scripts.

        // Request a SIGTERM if our parent dies.
        util::nix::request_parent_death_signal(Signal::SIGTERM)?;

        let transport = backend::create(&opts.backend_opts)?;
        let mut session = SessionHandler::init(&transport, opts.listen_port)?;
        println!("Listening on port {}", session.get_port());
        session.run_loop()?;
        return Ok(());
    }

    if opts.child {
        // This process is a child, which is supposed to stay running as a daemon.
        match session_child(opts.listen_port, &opts.backend_opts) {
            Ok(()) => process::exit(0),
            Err(e) => {
                // Report any error to parent process though stdout pipe.
                serde_json::to_writer::<io::Stdout, Result<SessionStartResult, String>>(
                    io::stdout(),
                    &Err(format!("{}", e)),
                )?;
                process::exit(1)
            }
        }
    }

    // Locate directory to use for .pid files
    let base_dirs = BaseDirs::new().unwrap();
    let run_user_dir = base_dirs
        .runtime_dir()
        .ok_or_else(|| anyhow!("No /run/user directory"))?;
    let run_file_fn = |port: u16| {
        let mut p = PathBuf::from(run_user_dir);
        p.push(format!("opentitansession.{}.pid", port));
        p
    };

    let value = if opts.stop {
        // Send signal to daemon process to stop
        stop_session(run_file_fn, opts.listen_port.unwrap_or(9900))?
    } else {
        // Fork a daemon process
        start_session(run_file_fn)?
    };
    println!("{}", serde_json::to_string_pretty(&value)?);
    Ok(())
}
