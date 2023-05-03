// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::borrow::BorrowMut;
use std::cell::{Cell, RefCell};
use std::ffi::OsStr;
use std::io::{self, ErrorKind, Read, Write};
use std::mem::size_of;
use std::net::{TcpStream, ToSocketAddrs};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use anyhow::{bail, ensure, Context, Result};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::dif::lc_ctrl::LcCtrlReg;
use crate::impl_serializable_error;
use crate::io::jtag::{Jtag, JtagError, JtagParams, JtagTap, RiscvCsr, RiscvGpr, RiscvReg};
use crate::util::parse_int::ParseInt;
use crate::util::printer;

/// Represents an OpenOCD server that we can interact with.
pub struct OpenOcdServer {
    /// JTAG parameters.
    opts: JtagParams,
    /// OpenOCD child process.
    openocd_server_process: RefCell<Option<Child>>,
    /// Stream to the telnet interface of OpenOCD.
    openocd_socket_stream: Cell<Option<TcpStream>>,
    /// Accumulators for OpenOCD stdout and stderr
    openocd_accumulated_stdout: Arc<Mutex<String>>,
    openocd_accumulated_stderr: Arc<Mutex<String>>,
    /// JTAG TAP OpenOCD is connected to.
    jtag_tap: Cell<Option<JtagTap>>,
}

/// Errors related to the OpenOCD server.
#[derive(Error, Debug, Deserialize, Serialize)]
pub enum OpenOcdServerError {
    #[error("OpenOCD server is not running")]
    OpenOcdNotRunning,
    #[error("Generic error {0}")]
    Generic(String),
}
impl_serializable_error!(OpenOcdServerError);

impl OpenOcdServer {
    /// Delay between polls to the OpenOCD server to prevent thrashing.
    const POLL_DELAY: Duration = Duration::from_millis(100);

    /// Create a new OpenOcdServer with the given JTAG options without starting OpenOCD.
    pub fn new(opts: &JtagParams) -> Result<OpenOcdServer> {
        Ok(OpenOcdServer {
            opts: opts.clone(),
            openocd_server_process: Default::default(),
            openocd_socket_stream: Default::default(),
            openocd_accumulated_stdout: Default::default(),
            openocd_accumulated_stderr: Default::default(),
            jtag_tap: Default::default(),
        })
    }

    /// Spawn the OpenOCD server and connect to it.
    fn start(&self, tap: JtagTap) -> Result<()> {
        // Check if a server was already started.
        if let Some(mut child) = self.openocd_server_process.take() {
            // If it's still running, it won't have an exit status.
            if child.try_wait()?.is_none() {
                self.openocd_server_process.replace(Some(child));
                bail!("OpenOCD server already running");
            }
        }

        let mut args = Vec::new();

        // Pass the path to the adapter config file if given.
        if let Some(cfg) = &self.opts.openocd_adapter_config {
            args.extend(["-f", cfg]);
        }

        // Because these commands are command-line args, they *must* end with
        // semicolons to satisfy the TCL lexer. When a TCL program is read from
        // a file, newlines are sufficient to separate statements.
        let adapter_speed_cmd = format!("adapter speed {}", self.opts.adapter_speed_khz);
        args.extend(["-c", adapter_speed_cmd.as_str()]);
        args.extend(["-c", "transport select jtag;"]);
        args.extend(["-c", "scan_chain;"]);

        // Pass through the config for the chosen TAP.
        let target = match tap {
            JtagTap::RiscvTap => &self.opts.openocd_riscv_target_config,
            JtagTap::LcTap => &self.opts.openocd_lc_target_config,
        };
        self.jtag_tap.set(Some(tap));
        if let Some(cfg) = &target {
            args.extend(["-f", cfg]);
        }

        // Use the default port explicity to avoid relying on it not changing.
        let port_cmd = format!("tcl_port {}", self.opts.openocd_port);
        args.extend(["-c", port_cmd.as_str()]);
        args.extend(["-c", "init;"]);

        log::info!("CWD: {:?}", std::env::current_dir());
        log::info!(
            "Spawning OpenOCD: {:?} {:?}",
            self.opts.openocd,
            args.join(" ")
        );

        let mut cmd = Command::new(&self.opts.openocd);
        cmd.args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let mut child = cmd.spawn().with_context(|| {
            let program = cmd.get_program();
            let args = cmd.get_args().collect::<Vec<_>>().join(OsStr::new(" "));
            format!("failed to spawn openocd: {program:?} {args:?}",)
        })?;
        // printer stdout and stderr
        let stdout = child.stdout.take().unwrap();
        let stderr = child.stderr.take().unwrap();
        let a = self.openocd_accumulated_stdout.clone();
        let b = self.openocd_accumulated_stderr.clone();
        std::thread::spawn(move || {
            printer::accumulate(stdout, concat!(module_path!(), "::stdout"), a)
        });
        std::thread::spawn(move || {
            printer::accumulate(stderr, concat!(module_path!(), "::stderr"), b)
        });

        self.openocd_server_process.replace(Some(child));

        log::info!("Connecting to OpenOCD tcl interface...");

        let addr = format!("localhost:{}", self.opts.openocd_port);
        let stream = Self::wait_for_socket(addr, self.opts.openocd_timeout)
            .context("failed to connect to OpenOCD socket")?;

        self.openocd_socket_stream.set(Some(stream));

        // Test the connection by asking for OpenOCD's version.
        let version = self
            .send_tcl_cmd("version")
            .context("failed to get OpenOCD version")?;
        log::info!("OpenOCD version: {version}");

        Ok(())
    }

    fn stop(&self) -> Result<()> {
        log::info!("Stopping OpenOCD...");

        let Some(mut child) = self.openocd_server_process.take() else {
            // OpenOCD wasn't started, do nothing.
            return Ok(());
        };

        // Ask the server nicely to shut down.
        self.send_tcl_cmd("shutdown")
            .context("failed to send shutdown command")?;

        // Wait for it to exit.
        child
            .wait()
            .context("failed to wait for OpenOCD server to exit")?;

        // Cleanup TAP selection.
        self.jtag_tap.set(None);

        // Close the connection.
        drop(self.openocd_server_process.take());

        Ok(())
    }

    /// Kill the server without waiting for it to exit.
    fn kill(&self) -> Result<()> {
        let Some(mut child) = self.openocd_server_process.take() else {
            // OpenOCD wasn't started, do nothing.
            return Ok(());
        };

        // Cleanup TAP selection.
        self.jtag_tap.set(None);

        child.kill()?;

        Ok(())
    }

    /// Send a TCL command to OpenOCD and wait for its response.
    fn send_tcl_cmd(&self, cmd: &str) -> Result<String> {
        // Take the stream. The stream will not be replaced on communication
        // errors, causing future commands to also fail.
        let Some(mut stream) = self.openocd_socket_stream.take() else {
            return Err(OpenOcdServerError::OpenOcdNotRunning.into());
        };

        // The protocol is to send the command followed by a `0x1a` byte,
        // see https://openocd.org/doc/html/Tcl-Scripting-API.html#Tcl-RPC-server
        stream
            .write_all(cmd.as_bytes())
            .context("failed to send a command to OpenOCD server")?;
        stream
            .write_all(&[0x1a])
            .context("failed to send the command terminator to OpenOCD server")?;

        stream.flush().context("failed to flush stream")?;

        let answer = stream
            .borrow_mut()
            .bytes()
            .take_while(|x| match x {
                Ok(x) => *x != 0x1a,
                _ => false,
            })
            .collect::<Result<_, _>>()
            .context("failed to read the result of a command from OpenOCD server")?;

        self.openocd_socket_stream.replace(Some(stream));
        String::from_utf8(answer).context("failed to parse OpenOCD response as UTF-8")
    }

    fn read_memory_impl<T: ParseInt>(&self, addr: u32, buf: &mut [T]) -> Result<usize> {
        // Ibex does not have a MMU so always tell OpenOCD that we are using physical addresses
        // otherwise it will try to translate the address through the (non-existent) MMU
        let cmd = format!(
            "read_memory 0x{addr:x} {width} {count} phys",
            width = 8 * size_of::<T>(),
            count = buf.len()
        );
        let response = self.send_tcl_cmd(cmd.as_str())?;
        response.trim().split(' ').try_fold(0, |idx, val| {
            if idx < buf.len() {
                buf[idx] = T::from_str(val).context(format!(
                    "expected response to be an hexadecimal byte, got '{response}'"
                ))?;
                Ok(idx + 1)
            } else {
                bail!("OpenOCD returned too much data on read".to_string())
            }
        })
    }

    fn write_memory_impl<T: ToString>(&self, addr: u32, buf: &[T]) -> Result<()> {
        // Convert data to space-separated strings.
        let data: Vec<_> = buf.iter().map(ToString::to_string).collect();
        let data_str = &data[..].join(" ");
        // See [read_memory] about physical addresses
        let cmd = format!(
            "write_memory 0x{addr:x} {width} {{ {data_str} }} phys",
            width = 8 * size_of::<T>()
        );
        let response = self.send_tcl_cmd(cmd.as_str())?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    /// Poll `addr` until it is bound and a socket can connect.
    fn wait_for_socket<A: ToSocketAddrs>(addr: A, timeout: Duration) -> io::Result<TcpStream> {
        let start = Instant::now();
        loop {
            log::warn!("Attempting to make tcp connection...");
            match TcpStream::connect(&addr) {
                // This is the error for addresses that aren't bound
                Err(e) if e.kind() == ErrorKind::ConnectionRefused => (),
                // This is error has been observed in CQ.
                Err(e) if e.kind() == ErrorKind::AddrNotAvailable => {
                    log::warn!("Got ErrorKind::AddrInUse on client socket, odd...");
                }
                // All other errors (and `Ok`s) we want to know about
                Err(e) => {
                    log::warn!("Error: {:?}", e.kind());

                    return Err(e);
                }
                socket => return socket,
            }

            // Delay between loops if there's enough time before timeout.
            if start.elapsed() + Self::POLL_DELAY < timeout {
                thread::sleep(Self::POLL_DELAY);
            } else {
                log::warn!("timeout");
                return Err(ErrorKind::TimedOut.into());
            }
        }
    }

    // Convert a RISC-V register name into a name that can be used
    // with read_register32.
    fn riscv_reg_name(&self, reg: &RiscvReg) -> &'static str {
        match reg {
            RiscvReg::GprByName(gpr) => match gpr {
                RiscvGpr::GP => "gp",
                RiscvGpr::SP => "sp",
            },
            RiscvReg::CsrByName(csr) => match csr {
                RiscvCsr::DPC => "dpc",
                RiscvCsr::PMPCFG0 => "pmpcfg0",
                RiscvCsr::PMPCFG1 => "pmpcfg1",
                RiscvCsr::PMPCFG2 => "pmpcfg2",
                RiscvCsr::PMPCFG3 => "pmpcfg3",
                RiscvCsr::PMPADDR0 => "pmpaddr0",
                RiscvCsr::PMPADDR15 => "pmpaddr15",
            },
        }
    }

    /// Read a register: this function does not attempt to translate the
    /// name or number of the register. If force is set, bypass OpenOCD's
    /// register cache.
    fn read_register<T: ParseInt>(&self, reg_name: &str, force: bool) -> Result<T> {
        let cmd = format!(
            "get_reg {} {{ {} }}",
            if force { "-force" } else { "" },
            reg_name,
        );
        let response = self.send_tcl_cmd(cmd.as_str())?;
        // the expected output format is 'reg_name 0xabcdef', e.g 'pc 0x10009858'
        let (out_reg_name, value) = response
            .trim()
            .split_once(' ')
            .context("expected response of the form 'reg value', got '{response}'")?;
        ensure!(
            out_reg_name == reg_name,
            "OpenOCD returned the value for register '{out_reg_name}' instead of '{reg_name}"
        );
        T::from_str(value).context(format!(
            "expected value to be an hexadecimal string, got '{value}'"
        ))
    }

    fn write_register<T: ToString>(&self, reg_name: &str, value: T) -> Result<()> {
        let cmd = format!("set_reg {{ {reg_name} {} }}", T::to_string(&value));
        let response = self.send_tcl_cmd(cmd.as_str())?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }
}

impl Drop for OpenOcdServer {
    fn drop(&mut self) {
        self.kill().ok();
    }
}

impl Jtag for OpenOcdServer {
    fn connect(&self, tap: JtagTap) -> Result<()> {
        self.start(tap)
    }

    fn disconnect(&self) -> Result<()> {
        self.stop()
    }

    fn read_lc_ctrl_reg(&self, reg: &LcCtrlReg) -> Result<u32> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::LcTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let reg_offset = reg.word_offset();
        let cmd = format!("riscv dmi_read 0x{reg_offset:x}");
        let response = self.send_tcl_cmd(cmd.as_str())?;

        let value = u32::from_str(response.trim()).context(format!(
            "expected response to be hexadecimal word, got '{response}'"
        ))?;

        Ok(value)
    }

    fn write_lc_ctrl_reg(&self, reg: &LcCtrlReg, value: u32) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::LcTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let reg_offset = reg.word_offset();
        let cmd = format!("riscv dmi_write 0x{reg_offset:x} 0x{value:x}");
        let response = self.send_tcl_cmd(cmd.as_str())?;

        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    fn read_memory(&self, addr: u32, buf: &mut [u8]) -> Result<usize> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        self.read_memory_impl(addr, buf)
    }

    fn read_memory32(&self, addr: u32, buf: &mut [u32]) -> Result<usize> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        self.read_memory_impl(addr, buf)
    }

    fn write_memory(&self, addr: u32, buf: &[u8]) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        self.write_memory_impl(addr, buf)
    }

    fn write_memory32(&self, addr: u32, buf: &[u32]) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        self.write_memory_impl(addr, buf)
    }

    fn halt(&self) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let response = self.send_tcl_cmd("halt")?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    fn resume(&self) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let response = self.send_tcl_cmd("resume")?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    fn resume_at(&self, addr: u32) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let cmd = format!("resume 0x{:x}", addr);
        let response = self.send_tcl_cmd(&cmd)?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    fn reset(&self, run: bool) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let cmd = format!("reset {}", if run { "run" } else { "halt" });
        let response = self.send_tcl_cmd(&cmd)?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    fn step(&self) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let response = self.send_tcl_cmd("step")?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    fn step_at(&self, addr: u32) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let cmd = format!("step 0x{:x}", addr);
        let response = self.send_tcl_cmd(&cmd)?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    fn read_riscv_reg(&self, reg: &RiscvReg) -> Result<u32> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        self.read_register::<u32>(self.riscv_reg_name(reg), true)
    }

    fn write_riscv_reg(&self, reg: &RiscvReg, val: u32) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        self.write_register(self.riscv_reg_name(reg), val)
    }
}
