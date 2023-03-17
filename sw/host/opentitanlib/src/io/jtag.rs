// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use structopt::StructOpt;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use crate::impl_serializable_error;

#[derive(Debug, StructOpt)]
pub struct JtagParams {
    #[structopt(long, help = "OpenOCD binary path.", default_value = "openocd")]
    pub openocd: String,

    #[structopt(long, help = "Path to OpenOCD JTAG adapter config file.")]
    openocd_adapter_config: String,
}

impl JtagParams {
    pub fn create(&self, transport: &TransportWrapper) -> Result<Rc<dyn Jtag>> {
        let jtag = transport.jtag(&self.openocd, &self.openocd_adapter_config)?;
        Ok(jtag)
    }
}

/// Errors related to the JTAG interface.
#[derive(Error, Debug, Deserialize, Serialize)]
pub enum JtagError {
    #[error("JTAG timeout")]
    Timeout,
    #[error("JTAG busy")]
    Busy,
    #[error("Generic error {0}")]
    Generic(String),
}
impl_serializable_error!(JtagError);

/// Represents an OpenOCD command sent over JTAG.
pub enum OpenOcdCmd {
    ReadLcCtrlReg(LcCtrlReg),
    WriteLcCtrlReg(LcCtrlReg, u32),
    // ReadCpuReg(IbexReg),
    // WriteCpuReg(IbexReg, u32),
    ReadMemory { addr: u32 },
    WriteMemory { addr: u32, value: u32 },
    Halt,
    Resume,
    Shutdown,
    Version,
}

/// Represents a (higher complexity) OpenOCD command sequence.
pub enum OpenOcdCmdSeq {
    /// Exits with a non-zero status when the register does not contain the
    /// given value.
    AssertLcCtrlRegEq(LcCtrlReg, u32),

    /// Polls the lc_ctrl register a finite number of times until its value
    /// matches the expectation.
    PollUntilLcCtrlRegEq(LcCtrlReg, u32),

    /// Performs a lifecycle state transition to the target lifecycle state.
    PerformLcTransition(DifLcCtrlState),
}

/// A trait which represents a JTAG interface.
pub trait Jtag {
    /// Starts an OpenOCD server to connect to the OpenTitan JTAG interface.
    fn start_openocd_server<'a>(
        &self,
        openocd: &'a str,
        openocd_adapter_config: &'a str,
    ) -> Result<()>;

    /// Stops the running OpenOCD server process.
    fn stop_openocd_server(&self) -> Result<()>;

    /// Runs an OpenOCD command over the JTAG interface.
    fn exec_openocd_cmd(&self, cmd: OpenOcdCmd) -> Result<()>;

    /// Runs a (higher complexity) OpenOCD command sequence.
    fn exec_openocd_cmd_seq(&self, cmd_seq: OpenOcdCmdSeq) -> Result<()>;
}
