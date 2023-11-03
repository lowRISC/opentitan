// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::io::{BufRead, BufReader, Write};
use std::mem::size_of;
use std::net::TcpStream;
use std::path::Path;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{bail, ensure, Context, Result};
use once_cell::sync::Lazy;
use regex::Regex;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::dif::lc_ctrl::LcCtrlReg;
use crate::impl_serializable_error;
use crate::io::jtag::{Jtag, JtagError, JtagParams, JtagTap, RiscvReg};
use crate::util::parse_int::ParseInt;
use crate::util::printer;

/// Represents an OpenOCD server that we can interact with.
pub struct OpenOcd {
    /// OpenOCD child process.
    server_process: Child,
    /// Receiving side of the stream to the telnet interface of OpenOCD.
    reader: BufReader<TcpStream>,
    /// Sending side of the stream to the telnet interface of OpenOCD.
    writer: TcpStream,
}

impl Drop for OpenOcd {
    fn drop(&mut self) {
        let _ = self.server_process.kill();
    }
}

impl OpenOcd {
    /// How long to wait for OpenOCD to get ready to accept a TCL connection.
    const OPENOCD_TCL_READY_TMO: Duration = Duration::from_secs(30);

    /// Wait until we see a particular message on the output.
    fn wait_until_regex_match<'a>(
        stderr: &mut impl BufRead,
        regex: &Regex,
        timeout: Duration,
        s: &'a mut String,
    ) -> Result<regex::Captures<'a>> {
        let start = Instant::now();
        loop {
            // NOTE the read could block indefinitely, a proper solution would involved spawning
            // a thread or using async.
            let n = stderr.read_line(s)?;
            if n == 0 {
                bail!("OpenOCD stopped before being ready?");
            }
            log::info!(target: concat!(module_path!(), "::stderr"), "{}", s);
            if regex.is_match(s) {
                // This is not a `if let Some(capture) = regex.captures(s) {}` to to Rust
                // borrow checker limitations. Can be modified if Polonius lands.
                return Ok(regex.captures(s).unwrap());
            }
            s.clear();

            if start.elapsed() >= timeout {
                bail!("OpenOCD did not become ready to accept a TCL connection");
            }
        }
    }

    /// Spawn an OpenOCD server with given path.
    pub fn spawn(path: &Path) -> Result<Self> {
        let mut cmd = Command::new(path);

        // Let OpenOCD choose which port to bind to, in order to never unnecesarily run into
        // issues due to a particular port already being in use.
        // We don't use the telnet and GDB ports so disable them.
        // The configuration will happen through the TCL interface, so use `noinit` to prevent
        // OpenOCD from transition to execution mode.
        cmd.arg("-c")
            .arg("tcl_port 0; telnet_port disabled; gdb_port disabled; noinit;");

        log::info!("CWD: {:?}", std::env::current_dir());
        log::info!("Spawning OpenOCD: {cmd:?}");

        cmd.stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let mut child = cmd
            .spawn()
            .with_context(|| format!("failed to spawn openocd: {cmd:?}",))?;
        let stdout = child.stdout.take().unwrap();
        let mut stderr = BufReader::new(child.stderr.take().unwrap());
        // Wait until we see 'Info : Listening on port XXX for tcl connections' before knowing
        // which port to connect to.
        log::info!("Waiting for OpenOCD to be ready to accept a TCL connection...");
        static READY_REGEX: Lazy<Regex> = Lazy::new(|| {
            Regex::new("Info : Listening on port ([0-9]+) for tcl connections").unwrap()
        });
        let mut buf = String::new();
        let regex_captures = Self::wait_until_regex_match(
            &mut stderr,
            &READY_REGEX,
            Self::OPENOCD_TCL_READY_TMO,
            &mut buf,
        )
        .context("OpenOCD was not ready in time to accept a connection")?;
        let openocd_port: u16 = regex_captures.get(1).unwrap().as_str().parse()?;
        // Print stdout and stderr with log
        std::thread::spawn(move || {
            printer::accumulate(
                stdout,
                concat!(module_path!(), "::stdout"),
                Default::default(),
            )
        });
        std::thread::spawn(move || {
            printer::accumulate(
                stderr,
                concat!(module_path!(), "::stderr"),
                Default::default(),
            )
        });

        let kill_guard = scopeguard::guard(child, |mut child| {
            let _ = child.kill();
        });

        log::info!("Connecting to OpenOCD tcl interface...");

        let stream = TcpStream::connect(("localhost", openocd_port))
            .context("failed to connect to OpenOCD socket")?;

        let mut connection = Self {
            server_process: scopeguard::ScopeGuard::into_inner(kill_guard),
            reader: BufReader::new(stream.try_clone()?),
            writer: stream,
        };

        // Test the connection by asking for OpenOCD's version.
        let version = connection.execute("version")?;
        log::info!("OpenOCD version: {version}");

        Ok(connection)
    }

    /// Send a string to OpenOCD Tcl interface.
    fn send(&mut self, cmd: &str) -> Result<()> {
        // The protocol is to send the command followed by a `0x1a` byte,
        // see https://openocd.org/doc/html/Tcl-Scripting-API.html#Tcl-RPC-server

        // Sanity check to ensure that the command string is not malformed.
        if cmd.contains('\x1A') {
            bail!("TCL command string should be contained inside the text to send");
        }

        self.writer
            .write_all(cmd.as_bytes())
            .context("failed to send a command to OpenOCD server")?;
        self.writer
            .write_all(&[0x1a])
            .context("failed to send the command terminator to OpenOCD server")?;
        self.writer.flush().context("failed to flush stream")?;
        Ok(())
    }

    fn recv(&mut self) -> Result<String> {
        let mut buf = Vec::new();
        self.reader.read_until(0x1A, &mut buf)?;
        if !buf.ends_with(b"\x1A") {
            bail!(OpenOcdError::PrematureExit);
        }
        buf.pop();
        String::from_utf8(buf).context("failed to parse OpenOCD response as UTF-8")
    }

    pub fn shutdown(mut self) -> Result<()> {
        self.execute("shutdown")?;
        // Wait for it to exit.
        self.server_process
            .wait()
            .context("failed to wait for OpenOCD server to exit")?;
        Ok(())
    }

    /// Send a TCL command to OpenOCD and wait for its response.
    pub fn execute(&mut self, cmd: &str) -> Result<String> {
        self.send(cmd)?;
        self.recv()
    }
}

/// An JTAG interface driver over OpenOCD.
pub struct OpenOcdJtagChain {
    /// Connection command for the particular adapter.
    adapter_command: String,
    /// JTAG parameters.
    opts: JtagParams,
    /// OpenOCD server instance.
    openocd_server: Cell<Option<OpenOcd>>,
    /// JTAG TAP OpenOCD is connected to.
    jtag_tap: Cell<Option<JtagTap>>,
}

/// Errors related to the OpenOCD server.
#[derive(Error, Debug, Deserialize, Serialize)]
pub enum OpenOcdError {
    #[error("OpenOCD server is not running")]
    OpenOcdNotRunning,
    #[error("OpenOCD server exists prematurely")]
    PrematureExit,
    #[error("Generic error {0}")]
    Generic(String),
}
impl_serializable_error!(OpenOcdError);

impl OpenOcdJtagChain {
    /// Create a new OpenOcdJtagChain with the given JTAG options without starting OpenOCD.
    pub fn new(adapter_command: String, opts: &JtagParams) -> Result<OpenOcdJtagChain> {
        Ok(OpenOcdJtagChain {
            adapter_command,
            opts: opts.clone(),
            openocd_server: Default::default(),
            jtag_tap: Default::default(),
        })
    }

    /// Spawn the OpenOCD server and connect to it.
    fn start(&self, tap: JtagTap) -> Result<()> {
        // Check if a server was already started.
        if self.openocd_server.take().is_some() {
            bail!("OpenOCD server already running");
        }

        let mut openocd = OpenOcd::spawn(&self.opts.openocd)?;

        openocd.execute(&self.adapter_command)?;
        openocd.execute(&format!("adapter speed {}", self.opts.adapter_speed_khz))?;
        openocd.execute("transport select jtag")?;
        openocd.execute("scan_chain")?;

        // Pass through the config for the chosen TAP.
        let target = match tap {
            JtagTap::RiscvTap => include_str!(env!("openocd_riscv_target_cfg")),
            JtagTap::LcTap => include_str!(env!("openocd_lc_target_cfg")),
        };
        self.jtag_tap.set(Some(tap));
        openocd.execute(target)?;

        // Finish initialisation.
        openocd.execute("init")?;

        self.openocd_server.replace(Some(openocd));

        Ok(())
    }

    fn stop(&self) -> Result<()> {
        log::info!("Stopping OpenOCD...");

        let Some(server) = self.openocd_server.take() else {
            // OpenOCD wasn't started, do nothing.
            return Ok(());
        };

        // Cleanup TAP selection.
        self.jtag_tap.set(None);

        server.shutdown()?;

        Ok(())
    }

    /// Send a TCL command to OpenOCD and wait for its response.
    fn send_tcl_cmd(&self, cmd: &str) -> Result<String> {
        // Take the server. The server will not be replaced on communication
        // errors, causing future commands to also fail.
        let Some(mut server) = self.openocd_server.take() else {
            return Err(OpenOcdError::OpenOcdNotRunning.into());
        };

        let ret = server.execute(cmd)?;
        self.openocd_server.replace(Some(server));
        Ok(ret)
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

    fn write_memory_impl<T: ToString>(&self, addr: u32, bigbuf: &[T]) -> Result<()> {
        const CHUNK_SIZE: usize = 1024;
        for (idx, buf) in bigbuf.chunks(CHUNK_SIZE).enumerate() {
            // Convert data to space-separated strings.
            let data: Vec<_> = buf.iter().map(ToString::to_string).collect();
            let data_str = &data[..].join(" ");
            // See [read_memory] about physical addresses
            let cmd = format!(
                "write_memory 0x{chunk_addr:x} {width} {{ {data_str} }} phys",
                chunk_addr = addr + (idx * CHUNK_SIZE * size_of::<T>()) as u32,
                width = 8 * size_of::<T>()
            );
            let response = self.send_tcl_cmd(cmd.as_str())?;
            if !response.is_empty() {
                bail!("unexpected response: '{response}'");
            }
        }

        Ok(())
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

impl Jtag for OpenOcdJtagChain {
    fn connect(&self, tap: JtagTap) -> Result<()> {
        self.start(tap)
    }

    fn disconnect(&self) -> Result<()> {
        self.stop()
    }

    fn get_tap(&self) -> Option<JtagTap> {
        self.jtag_tap.get()
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

    fn wait_halt(&self, timeout: Duration) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        let cmd = format!("wait_halt {}", timeout.as_millis());
        let response = self.send_tcl_cmd(cmd.as_str())?;
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
        self.read_register::<u32>(reg.name(), true)
    }

    fn write_riscv_reg(&self, reg: &RiscvReg, val: u32) -> Result<()> {
        ensure!(
            matches!(self.jtag_tap.get().unwrap(), JtagTap::RiscvTap),
            JtagError::Tap(self.jtag_tap.get().unwrap())
        );
        self.write_register(reg.name(), val)
    }

    fn set_breakpoint(&self, address: u32, hw: bool) -> Result<()> {
        let cmd = format!("bp {:#x} 2{}", address, if hw { " hw" } else { "" });
        let response = self.send_tcl_cmd(&cmd)?;
        if !response.starts_with("breakpoint set at ") {
            bail!("unexpected response: '{response}'");
        }
        Ok(())
    }

    fn remove_breakpoint(&self, addr: u32) -> Result<()> {
        let cmd = format!("rbp {:#x}", addr);
        let response = self.send_tcl_cmd(&cmd)?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }
        Ok(())
    }

    fn remove_all_breakpoints(&self) -> Result<()> {
        let response = self.send_tcl_cmd("rbp all")?;
        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }
        Ok(())
    }
}
