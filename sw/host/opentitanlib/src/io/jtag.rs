// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use crate::app::TransportWrapper;
use crate::dif::lc_ctrl::LcCtrlReg;
use crate::impl_serializable_error;

#[derive(Debug, Args, Clone)]
pub struct JtagParams {
    /// OpenOCD binary path.
    #[arg(long, default_value = "openocd")]
    pub openocd: PathBuf,

    #[arg(long, default_value = "200")]
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
    fn tap(&self) -> Option<JtagTap>;

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

    /// Wait until the target halt. This does NOT halt the target on timeout.
    fn wait_halt(&self, timeout: Duration) -> Result<()>;

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

    /// Set a breakpoint at the given address.
    fn set_breakpoint(&self, addr: u32, hw: bool) -> Result<()>;
    fn remove_breakpoint(&self, addr: u32) -> Result<()>;
    fn remove_all_breakpoints(&self) -> Result<()>;
}

/// Available JTAG TAPs (software TAPS) in OpenTitan.
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq)]
pub enum JtagTap {
    /// RISC-V core's TAP.
    RiscvTap,
    /// Lifecycle Controller's TAP.
    LcTap,
}

/// List of RISC-V general purpose registers
#[derive(Clone, Copy, Debug, Deserialize, Serialize, strum::IntoStaticStr)]
#[strum(serialize_all = "lowercase")]
pub enum RiscvGpr {
    RA,
    SP,
    GP,
    TP,
    T0,
    T1,
    T2,
    FP,
    S1,
    A0,
    A1,
    A2,
    A3,
    A4,
    A5,
    A6,
    A7,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    S8,
    S9,
    S10,
    S11,
    T3,
    T4,
    T5,
    T6,
}

impl RiscvGpr {
    /// Get the register name as a string.
    pub fn name(self) -> &'static str {
        self.into()
    }
}

/// List of useful RISC-V control and status registers
#[derive(Clone, Copy, Debug, Deserialize, Serialize, strum::IntoStaticStr)]
#[strum(serialize_all = "lowercase")]
#[non_exhaustive]
pub enum RiscvCsr {
    MSTATUS,
    MISA,
    MIE,
    MTVEC,
    MCOUNTINHIBIT,
    MHPMEVENT3,
    MHPMEVENT4,
    MHPMEVENT5,
    MHPMEVENT6,
    MHPMEVENT7,
    MHPMEVENT8,
    MHPMEVENT9,
    MHPMEVENT10,
    MHPMEVENT11,
    MHPMEVENT12,
    MHPMEVENT13,
    MHPMEVENT14,
    MHPMEVENT15,
    MHPMEVENT16,
    MHPMEVENT17,
    MHPMEVENT18,
    MHPMEVENT19,
    MHPMEVENT20,
    MHPMEVENT21,
    MHPMEVENT22,
    MHPMEVENT23,
    MHPMEVENT24,
    MHPMEVENT25,
    MHPMEVENT26,
    MHPMEVENT27,
    MHPMEVENT28,
    MHPMEVENT29,
    MHPMEVENT30,
    MHPMEVENT31,
    MSCRATCH,
    MEPC,
    MCAUSE,
    MTVAL,
    MIP,
    PMPCFG0,
    PMPCFG1,
    PMPCFG2,
    PMPCFG3,
    PMPADDR0,
    PMPADDR1,
    PMPADDR2,
    PMPADDR3,
    PMPADDR4,
    PMPADDR5,
    PMPADDR6,
    PMPADDR7,
    PMPADDR8,
    PMPADDR9,
    PMPADDR10,
    PMPADDR11,
    PMPADDR12,
    PMPADDR13,
    PMPADDR14,
    PMPADDR15,
    SCONTEXT,
    MSECCFG,
    MSECCFGH,
    TSELECT,
    TDATA1,
    TDATA2,
    TDATA3,
    MCONTEXT,
    MSCONTEXT,
    DCSR,
    DPC,
    DSCRATCH0,
    DSCRATCH1,
    MCYCLE,
    MINSTRET,
    MHPMCOUNTER3,
    MHPMCOUNTER4,
    MHPMCOUNTER5,
    MHPMCOUNTER6,
    MHPMCOUNTER7,
    MHPMCOUNTER8,
    MHPMCOUNTER9,
    MHPMCOUNTER10,
    MHPMCOUNTER11,
    MHPMCOUNTER12,
    MHPMCOUNTER13,
    MHPMCOUNTER14,
    MHPMCOUNTER15,
    MHPMCOUNTER16,
    MHPMCOUNTER17,
    MHPMCOUNTER18,
    MHPMCOUNTER19,
    MHPMCOUNTER20,
    MHPMCOUNTER21,
    MHPMCOUNTER22,
    MHPMCOUNTER23,
    MHPMCOUNTER24,
    MHPMCOUNTER25,
    MHPMCOUNTER26,
    MHPMCOUNTER27,
    MHPMCOUNTER28,
    MHPMCOUNTER29,
    MHPMCOUNTER30,
    MHPMCOUNTER31,
    MCYCLEH,
    MINSTRETH,
    MHPMCOUNTER3H,
    MHPMCOUNTER4H,
    MHPMCOUNTER5H,
    MHPMCOUNTER6H,
    MHPMCOUNTER7H,
    MHPMCOUNTER8H,
    MHPMCOUNTER9H,
    MHPMCOUNTER10H,
    MHPMCOUNTER11H,
    MHPMCOUNTER12H,
    MHPMCOUNTER13H,
    MHPMCOUNTER14H,
    MHPMCOUNTER15H,
    MHPMCOUNTER16H,
    MHPMCOUNTER17H,
    MHPMCOUNTER18H,
    MHPMCOUNTER19H,
    MHPMCOUNTER20H,
    MHPMCOUNTER21H,
    MHPMCOUNTER22H,
    MHPMCOUNTER23H,
    MHPMCOUNTER24H,
    MHPMCOUNTER25H,
    MHPMCOUNTER26H,
    MHPMCOUNTER27H,
    MHPMCOUNTER28H,
    MHPMCOUNTER29H,
    MHPMCOUNTER30H,
    MHPMCOUNTER31H,
    MVENDORID,
    MARCHID,
    MIMPID,
    MHARTID,

    // Custom CSRs, those are exposed with "csr_" prefix.
    #[strum(serialize = "csr_cpuctrl")]
    CPUCTRL,
    #[strum(serialize = "csr_secureseed")]
    SECURESEED,
}

impl RiscvCsr {
    /// Get the register name as a string.
    pub fn name(self) -> &'static str {
        self.into()
    }
}

/// Available registers for RISC-V TAP
#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
pub enum RiscvReg {
    /// General Purpose Register
    Gpr(RiscvGpr),
    /// Control and Status Register
    Csr(RiscvCsr),
}

impl RiscvReg {
    /// Get the register name as a string.
    pub fn name(self) -> &'static str {
        match self {
            Self::Gpr(gpr) => gpr.name(),
            Self::Csr(csr) => csr.name(),
        }
    }
}

impl From<RiscvGpr> for RiscvReg {
    fn from(gpr: RiscvGpr) -> Self {
        Self::Gpr(gpr)
    }
}

impl From<RiscvCsr> for RiscvReg {
    fn from(csr: RiscvCsr) -> Self {
        Self::Csr(csr)
    }
}
