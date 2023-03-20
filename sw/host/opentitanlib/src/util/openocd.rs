// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::borrow::BorrowMut;
use std::cell::{Cell, RefCell};
use std::ffi::OsStr;
use std::io::Read;
use std::io::Write;
use std::net::TcpStream;
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::Duration;

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::dif::lc_ctrl::LcCtrlReg;
use crate::impl_serializable_error;
use crate::io::jtag::{Jtag, JtagParams, JtagTap};
use crate::util::parse_int::ParseInt;

/// Represents an OpenOCD server that we can interact with.
pub struct OpenOcdServer {
    /// JTAG parameters.
    opts: JtagParams,
    /// OpenOCD child process.
    openocd_server_process: RefCell<Option<Child>>,
    /// Stream to the telnet interface of OpenOCD.
    openocd_socket_stream: Cell<Option<TcpStream>>,
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
    /// Create a new OpenOcdServer with the given JTAG options without starting OpenOCD.
    pub fn new(opts: &JtagParams) -> Result<OpenOcdServer> {
        Ok(OpenOcdServer {
            opts: opts.clone(),
            openocd_server_process: Default::default(),
            openocd_socket_stream: Default::default(),
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
            args.extend(["-f", &cfg]);
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
        if let Some(cfg) = &target {
            args.extend(["-f", &cfg]);
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

        // TODO: forward output/stderr to loggin using a worker, like for verilator.
        let mut cmd = Command::new(&self.opts.openocd);
        cmd.args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());
        let child = cmd.spawn().with_context(|| {
            let program = cmd.get_program();
            let args = cmd.get_args().collect::<Vec<_>>().join(OsStr::new(" "));
            format!("failed to spawn openocd: {program:?} {args:?}",)
        })?;
        self.openocd_server_process.replace(Some(child));

        // Give OpenOCD time to start up.
        thread::sleep(Duration::from_millis(1000));

        log::info!("Connecting to OpenOCD tcl interface...");

        let stream = TcpStream::connect(format!("localhost:{}", self.opts.openocd_port))
            .context("failed to connect to openocd telnet interface")?;
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

        // TODO: send "shutdown" command and wait before killing the process.
        Ok(child.kill()?)
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
}

impl Drop for OpenOcdServer {
    fn drop(&mut self) {
        self.stop().ok();
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
        let reg_offset = reg.word_offset();
        let cmd = format!("riscv dmi_read 0x{reg_offset:x}");
        let response = self.send_tcl_cmd(cmd.as_str())?;

        let value = u32::from_str(response.trim()).context(format!(
            "expected response to be hexadecimal word, got '{response}'"
        ))?;

        Ok(value)
    }

    fn write_lc_ctrl_reg(&self, reg: &LcCtrlReg, value: u32) -> Result<()> {
        let reg_offset = reg.word_offset();
        let cmd = format!("riscv dmi_write 0x{reg_offset:x} 0x{value:x}");
        let response = self.send_tcl_cmd(cmd.as_str())?;

        if !response.is_empty() {
            bail!("unexpected response: '{response}'");
        }

        Ok(())
    }

    fn read_memory(&self, addr: u32, buf: &mut [u8]) -> Result<u32> {
        let cmd = format!("read_memory 0x{addr:x} 8 {count}", count = buf.len());
        let _response = self.send_tcl_cmd(cmd.as_str())?;
        todo!("handle response from OpenOCD");
    }

    fn write_memory(&self, addr: u32, buf: &[u8]) -> Result<()> {
        // Convert data to space-separated strings.
        let data: Vec<_> = buf.iter().map(ToString::to_string).collect();
        let data_str = &data[..].join(" ");

        let cmd = format!("write_memory 0x{addr:x} 8 {{ {data_str} }}");
        let _response = self.send_tcl_cmd(cmd.as_str())?;

        todo!("handle response from OpenOCD");
    }

    fn halt(&self) -> Result<()> {
        let _response = self.send_tcl_cmd("halt")?;
        todo!("handle response from OpenOCD");
    }

    fn resume(&self) -> Result<()> {
        let _response = self.send_tcl_cmd("resume")?;
        todo!("handle response from OpenOCD");
    }
}
