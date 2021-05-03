use anyhow::{anyhow, Result};
use erased_serde::Serialize;
use nix::unistd::isatty;
use raw_tty::TtyModeGuard;
use regex::Regex;
use std::fs::File;
use std::io;
use std::io::{ErrorKind, Read, Write};
use std::os::unix::io::AsRawFd;
use std::time::{Duration, Instant};
use structopt::StructOpt;

use crate::command::CommandDispatch;
use opentitanlib::io::uart::Uart;
use opentitanlib::transport::{Capability, Transport};
use opentitanlib::util::file;

#[derive(Debug, StructOpt)]
pub struct Console {
    #[structopt(short, long, help = "Do not print console start end exit messages.")]
    quiet: bool,

    #[structopt(short, long, help = "Log console output to a file")]
    logfile: Option<String>,

    #[structopt(short, long, help = "Exit after a timeout in seconds.")]
    timeout: Option<u64>,

    #[structopt(long, help = "Exit with success if the specified regex is matched.")]
    exit_success: Option<String>,

    #[structopt(long, help = "Exit with failure if the specified regex is matched.")]
    exit_failure: Option<String>,
}

impl CommandDispatch for Console {
    fn run(&self, transport: &mut dyn Transport) -> Result<Option<Box<dyn Serialize>>> {
        // We need the UART for the console command to operate.
        transport.capabilities().request(Capability::UART).ok()?;
        let mut stdout = std::io::stdout();
        let mut stdin = std::io::stdin();

        // Set up resources specified by the command line parameters.
        let logfile = if let Some(filename) = &self.logfile {
            Some(File::create(filename)?)
        } else {
            None
        };
        let deadline = if let Some(timeout) = self.timeout {
            Some(Instant::now() + Duration::new(timeout, 0))
        } else {
            None
        };
        let exit_success = if let Some(rx) = &self.exit_success {
            Some(Regex::new(rx)?)
        } else {
            None
        };
        let exit_failure = if let Some(rx) = &self.exit_failure {
            Some(Regex::new(rx)?)
        } else {
            None
        };

        let mut console = InnerConsole {
            logfile: logfile,
            deadline: deadline,
            exit_success: exit_success,
            exit_failure: exit_failure,
            ..Default::default()
        };

        if !self.quiet {
            println!("Starting interactive console");
            println!("[CTRL+C] to exit.\n");
        }
        {
            // Put the terminal into raw mode.  The tty guard will restore the
            // console settings when it goes out of scope.
            let _stdin_guard = if isatty(stdin.as_raw_fd())? {
                let mut guard = TtyModeGuard::new(stdin.as_raw_fd())?;
                guard.set_raw_mode()?;
                Some(guard)
            } else {
                None
            };
            let _stdout_guard = if isatty(stdout.as_raw_fd())? {
                let mut guard = TtyModeGuard::new(stdout.as_raw_fd())?;
                guard.set_raw_mode()?;
                Some(guard)
            } else {
                None
            };
            console.interact(transport, &mut stdin, &mut stdout)?;
        }
        if !self.quiet {
            println!("\n\nExiting interactive console.");
        }
        Ok(None)
    }
}

#[derive(Default)]
struct InnerConsole {
    logfile: Option<File>,
    deadline: Option<Instant>,
    exit_success: Option<Regex>,
    exit_failure: Option<Regex>,
    buffer: String,
}

enum ExitStatus {
    None,
    ExitSuccess,
    ExitFailure,
}

impl InnerConsole {
    const CTRL_C: u8 = 3;
    const BUFFER_LEN: usize = 1024;

    // Runs an interactive console until CTRL_C is received.
    fn interact<R>(
        &mut self,
        transport: &mut dyn Transport,
        stdin: &mut R,
        stdout: &mut impl Write,
    ) -> Result<()>
    where
        R: Read + AsRawFd,
    {
        let mut uart = transport.uart()?;
        let mut buf = [0u8; 256];

        loop {
            if let Some(deadline) = self.deadline {
                if Instant::now() > deadline {
                    // If we have an exit success condition, then a timeout
                    // should be an error.
                    if self.exit_success.is_some() {
                        return Err(anyhow!("Console timeout exceeded"));
                    } else {
                        break;
                    }
                }
            }

            // This loop _should_ really use `poll` to learn when the
            // console or uart file descriptors become ready, but some UART
            // backends will bury their implementation in libusb and make
            // discovering the file descriptor difficult or impossible.
            //
            // As a pragmatic implementation detail, we wait for the UART
            // for a short period of time and then service the console.

            // Check for input on the uart.
            match self.uart_read(&mut *uart, Duration::from_millis(10), stdout)? {
                ExitStatus::None => {}
                ExitStatus::ExitSuccess => {
                    break;
                }
                ExitStatus::ExitFailure => {
                    return Err(anyhow!("Matched exit_failure expression"));
                }
            };

            // Wait for input from the user.
            match file::wait_read_timeout(&*stdin, Duration::from_millis(0)) {
                Ok(_) => {
                    let len = stdin.read(&mut buf)?;
                    if len == 1 && buf[0] == InnerConsole::CTRL_C {
                        break;
                    }
                    uart.write(&buf[..len])?;
                }
                Err(_) => {
                    // Can only be timeout.  Do nothing.
                }
            };
        }
        Ok(())
    }

    // Maintain a buffer for the exit regexes to match against.
    fn append_buffer(&mut self, data: &[u8]) {
        self.buffer.push_str(&String::from_utf8_lossy(&data[..]));
        if self.buffer.len() > InnerConsole::BUFFER_LEN {
            let (_, end) = self
                .buffer
                .split_at(self.buffer.len() - InnerConsole::BUFFER_LEN);
            self.buffer = end.to_string();
        }
    }

    // Read from the uart and process the data read.
    fn uart_read(
        &mut self,
        uart: &mut dyn Uart,
        timeout: Duration,
        stdout: &mut impl Write,
    ) -> Result<ExitStatus> {
        let mut buf = [0u8; 256];
        match uart.read_timeout(&mut buf, timeout) {
            Ok(len) => {
                stdout.write_all(&buf[..len])?;
                stdout.flush()?;

                // If we're logging, save it to the logfile.
                if let Some(logfile) = &mut self.logfile {
                    logfile.write_all(&buf[..len])?;
                }

                // If we have exit condition regexes check them.
                self.append_buffer(&buf[..len]);
                if self
                    .exit_success
                    .as_ref()
                    .map(|rx| rx.is_match(&self.buffer))
                    == Some(true)
                {
                    return Ok(ExitStatus::ExitSuccess);
                }
                if self
                    .exit_failure
                    .as_ref()
                    .map(|rx| rx.is_match(&self.buffer))
                    == Some(true)
                {
                    return Ok(ExitStatus::ExitFailure);
                }
            }
            Err(e) => {
                // If we got a timeout from the uart, ignore it.
                // Return all other errors.
                if let Some(ioerr) = e.downcast_ref::<io::Error>() {
                    if ioerr.kind() != ErrorKind::TimedOut {
                        return Err(e);
                    }
                } else {
                    return Err(e);
                }
            }
        }
        Ok(ExitStatus::None)
    }
}
