// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result, anyhow, bail};
use clap::Parser;
use directories::{BaseDirs, ProjectDirs};
use erased_serde::Serialize;
use log::LevelFilter;
use rustix::process::{Pid, Signal};
use std::env::{self, ArgsOs, args_os};
use std::ffi::OsString;
use std::fs::{self, File, read_to_string};
use std::io::{self, ErrorKind, Read, Write};
use std::iter::Iterator;
use std::path::PathBuf;
use std::process::{self, Command, Stdio};
use std::str::FromStr;
use std::time::Duration;

use opentitanlib::backend;
use ot_proxy::SessionHandler;

#[derive(Debug, Parser)]
#[command(
    name = "opentitansession",
    about = "A tool for interacting with OpenTitan chips."
)]
struct Opts {
    /// Filename of a default flagsfile.  Relative to $XDG_CONFIG_HOME/opentitantool.
    #[arg(long, value_parser = PathBuf::from_str, default_value = "config")]
    rcfile: PathBuf,

    #[arg(long, default_value = "off")]
    logging: LevelFilter,

    #[command(flatten)]
    backend_opts: backend::BackendOpts,

    /// Stop a running session, optionally combine with --listen_port for disambiguation.
    #[arg(long, conflicts_with = "foreground")]
    stop: bool,

    /// Optional, defaults to 9900 or nearest higher available port.
    #[arg(long)]
    listen_port: Option<u16>,

    /// Start session, staying in foreground (do not daemonize).  Session process will terminate if its parent dies.
    #[arg(long)]
    foreground: bool,

    /// Internal, used to tell the child process to run as a daemon.
    #[arg(long)]
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

    let mut buf = Vec::new();
    child.stdout.as_mut().unwrap().read_to_end(&mut buf)?;

    // Child process exited. In this case the child process has reported the error, so
    // we should just exit with the same error code.
    if buf.is_empty() {
        let exit_code = child.wait()?.code().unwrap_or(1);
        anyhow::ensure!(exit_code != 0);
        process::exit(exit_code);
    }

    let result: SessionStartResult = serde_json::from_slice(&buf)?;

    // Create a pid file corresponding to the requested TCP port.
    let path = run_file_fn(result.port);
    File::create(path)?.write_all(format!("{}\n", child.id()).as_bytes())?;
    Ok(Box::new(result))
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct SessionStopResult {}

/// Load .pid file based on given port number, and send SIGTERM to the process identified in the
/// file, to request the daemon gracefully shut down.
fn stop_session(run_file_fn: impl FnOnce(u16) -> PathBuf, port: u16) -> Result<Box<dyn Serialize>> {
    // Read the pid file corresponding to the requested TCP port.
    let path = run_file_fn(port);
    let pid = FromStr::from_str(fs::read_to_string(&path)?.trim())?;
    let pid = Pid::from_raw(pid).context("Pid is not valid")?;
    // Send signal to daemon process, asking it to terminate.
    rustix::process::kill_process(pid, Signal::TERM)?;
    // Wait for daemon process to stop.
    loop {
        std::thread::sleep(Duration::from_millis(100));
        // Send "signal 0", meaning that the kernel performs error checks (among those, checking
        // that the target process exists), without actually sending any signal.
        match rustix::process::test_kill_process(pid) {
            Ok(()) => (), // Process still running, repeat.
            Err(rustix::io::Errno::SRCH) => {
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

    if !opts.foreground && !opts.child {
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
        return Ok(());
    }

    // Open connection to transport backend (HyperDebug or other debugger device) based on
    // command line arguments.
    let transport = backend::create(&opts.backend_opts)?;

    // Bind to TCP socket, in preparation for servicing requests from network.
    let mut session = SessionHandler::init(transport, opts.listen_port)?;

    if opts.foreground {
        // Request a SIGTERM if our parent dies.
        rustix::process::set_parent_process_death_signal(Some(Signal::TERM))?;

        println!("Listening on port {}", session.get_port());
    } else {
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
        rustix::stdio::dup2_stderr(File::open("/dev/null")?)?;

        // After severing the only connection to the controlling terminal inherited from the parent,
        // we can now establish a new Unix "session" for this process, which will not be
        // "controlled" by any terminal.  This means that this daemon will not be killed by SIGHUP,
        // in case the terminal that was used for running `session start` is later closed.
        rustix::process::setsid()?;

        // Report startup success to parent process.
        serde_json::to_writer::<io::Stdout, SessionStartResult>(
            io::stdout(),
            &SessionStartResult {
                port: session.get_port(),
            },
        )?;
        io::stdout().flush()?;

        // Closing the standard output pipe is the signal to the parent process that this child has
        // started up successfully.  We close the pipe indirectly, by replacing stdout file descriptor
        // with one pointing to /dev/null.  This will ensure that any subsequent accidentally
        // executed println!() will be a no-op, rather than trigger termination via SIGPIPE.
        rustix::stdio::dup2_stdout(io::stderr())?;
    }

    // Indefinitely run command processing loop in this daemon process.
    session.run_loop()
}
