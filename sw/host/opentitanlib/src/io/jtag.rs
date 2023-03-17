// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::rc::Rc;
use structopt::StructOpt;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::dif::lc_ctrl::LcCtrlReg;
use crate::impl_serializable_error;

#[derive(Debug, StructOpt)]
pub struct JtagParams {
    /// OpenOCD binary path.
    #[structopt(long, default_value = "openocd")]
    pub openocd: PathBuf,

    /// Path to OpenOCD JTAG adapter config file.
    #[structopt(long)]
    pub openocd_adapter_config: Option<String>,

    /// Path to OpenOCD JTAG target config file for the RISC-V TAP.
    #[structopt(long)]
    pub openocd_riscv_target_config: Option<String>,

    /// Path to OpenOCD JTAG target config file for the LC TAP.
    #[structopt(long)]
    pub openocd_lc_target_config: Option<String>,

    /// Port used to start and connect to OpenOCD over.
    #[structopt(long, default_value = "6666")]
    pub openocd_port: u16,

    #[structopt(long, default_value = "200")]
    pub adapter_speed_khz: u64,
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

/// A trait which represents a JTAG interface.
pub trait Jtag {
    /// Connect to the given JTAG TAP.
    fn connect(&self, tap: JtagTap) -> Result<()>;
    /// Disconnect from the TAP.
    fn disconnect(&self) -> Result<()>;

    // Commands

    /// Read a lifecycle controller register.
    fn read_lc_ctrl_reg(&self, reg: &LcCtrlReg) -> Result<u32>;

    /// Write a value to a lifecycle controller register.
    fn write_lc_ctrl_reg(&self, reg: &LcCtrlReg, value: u32) -> Result<()>;

    /// Read bytes from memory into the provided buffer.
    ///
    /// On success, returns the number of bytes read.
    fn read_memory(&self, addr: u32, buf: &mut [u8]) -> Result<u32>;

    /// Write bytes to memory.
    fn write_memory(&self, addr: u32, buf: &[u8]) -> Result<()>;

    /// Send a HALT command over Jtag.
    fn halt(&self) -> Result<()>;

    /// Send a RESUME command over Jtag.
    fn resume(&self) -> Result<()>;
}

/// Available JTAG TAPs (software TAPS) in OpenTitan.
#[derive(Clone, Copy, Debug)]
pub enum JtagTap {
    /// RISC-V core's TAP.
    RiscvTap,
    /// Lifecycle Controller's TAP.
    LcTap,
}
