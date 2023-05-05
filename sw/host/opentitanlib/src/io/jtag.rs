// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use structopt::StructOpt;
use thiserror::Error;

use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use crate::app::TransportWrapper;
use crate::dif::lc_ctrl::LcCtrlReg;
use crate::impl_serializable_error;

#[derive(Debug, StructOpt, Clone)]
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

    /// Timeout when waiting for OpenOCD to start.
    #[structopt(long, parse(try_from_str=humantime::parse_duration), default_value = "3s")]
    pub openocd_timeout: Duration,

    #[structopt(long, default_value = "200")]
    pub adapter_speed_khz: u64,
}

impl JtagParams {
    pub fn create(&self, transport: &TransportWrapper) -> Result<Rc<dyn Jtag>> {
        let jtag = transport.jtag(self)?;
        Ok(jtag)
    }
}

/// Errors related to the JTAG interface.
#[derive(Error, Debug, Deserialize, Serialize)]
pub enum JtagError {
    #[error("Operation not valid on selected JTAG TAP: {0:?}")]
    Tap(JtagTap),
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
    /// Get TAP we are currently connected too.
    fn get_tap(&self) -> Option<JtagTap>;

    // Commands

    /// Read a lifecycle controller register.
    fn read_lc_ctrl_reg(&self, reg: &LcCtrlReg) -> Result<u32>;

    /// Write a value to a lifecycle controller register.
    fn write_lc_ctrl_reg(&self, reg: &LcCtrlReg, value: u32) -> Result<()>;

    /// Read bytes/words from memory into the provided buffer.
    /// When reading bytes, each memory access is 8 bits.
    /// When reading words, each memory access is 32 bit. If the hardware
    /// does not support unaligned memory accesses, this function will fail.
    ///
    /// On success, returns the number of bytes/words read.
    fn read_memory(&self, addr: u32, buf: &mut [u8]) -> Result<usize>;
    fn read_memory32(&self, addr: u32, buf: &mut [u32]) -> Result<usize>;

    /// Write bytes/words to memory.
    fn write_memory(&self, addr: u32, buf: &[u8]) -> Result<()>;
    fn write_memory32(&self, addr: u32, buf: &[u32]) -> Result<()>;

    /// Halt execution.
    fn halt(&self) -> Result<()>;

    /// Resume execution at its current code position.
    fn resume(&self) -> Result<()>;
    /// Resume execution at the specified address.
    fn resume_at(&self, addr: u32) -> Result<()>;

    /// Single-step the target at its current code position.
    fn step(&self) -> Result<()>;
    /// Single-step the target at the specified address.
    fn step_at(&self, addr: u32) -> Result<()>;

    /// Reset the target as hard as possible.
    /// If run is true, the target will start running code immediately
    /// after reset, otherwise it will be halted immediately.
    fn reset(&self, run: bool) -> Result<()>;

    /// Read/write a RISC-V register
    fn read_riscv_reg(&self, reg: &RiscvReg) -> Result<u32>;
    fn write_riscv_reg(&self, reg: &RiscvReg, val: u32) -> Result<()>;
}

/// Available JTAG TAPs (software TAPS) in OpenTitan.
#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub enum JtagTap {
    /// RISC-V core's TAP.
    RiscvTap,
    /// Lifecycle Controller's TAP.
    LcTap,
}

/// List of useful RISC-V general purpose registers
#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub enum RiscvGpr {
    GP,
    SP,
}

/// List of useful RISC-V control and status registers
#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub enum RiscvCsr {
    DPC,
    PMPCFG0,
    PMPCFG1,
    PMPCFG2,
    PMPCFG3,
    PMPADDR0,
    PMPADDR15,
}

/// Available registers for RISC-V TAP
#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub enum RiscvReg {
    /// General Purpose Register
    GprByName(RiscvGpr),
    /// Control and Status Register
    CsrByName(RiscvCsr),
}
