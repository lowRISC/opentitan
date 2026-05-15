// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use std::path::PathBuf;
use std::time::Duration;

use ot_hal::dif::lc_ctrl::LcCtrlReg;

use crate::app::TransportWrapper;
use crate::debug::openocd::OpenOcd;
use crate::impl_serializable_error;

#[derive(Debug, Args, Clone)]
pub struct JtagParams {
    /// Which JTAG interface to use
    #[arg(long, default_value = "openocd")]
    pub jtag_interface: String,

    /// OpenOCD binary path.
    #[arg(long, default_value = "openocd")]
    pub openocd: PathBuf,

    #[arg(long, default_value = "1000")]
    pub adapter_speed_khz: u64,

    #[arg(long, default_value = "false")]
    pub log_stdio: bool,

    #[arg(
        long,
        help = "used to select a specific JTAG probe when multiple probes are available"
    )]
    pub jtag_usb_serial: Option<String>,
}

impl JtagParams {
    pub fn create<'t>(&self, transport: &'t TransportWrapper) -> Result<Box<dyn JtagChain + 't>> {
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
///
/// JTAG lines form a daisy-chained topology and can connect multiple TAPs together in a chain.
/// This trait represents an adaptor that has been configured to connect to a given JTAG chain,
/// but have not yet been configured to only access a particular TAP.
pub trait JtagChain {
    /// Connect to the given JTAG TAP on this chain.
    fn connect(self: Box<Self>, tap: JtagTap) -> Result<Box<dyn Jtag>>;

    // Stop further setup and returns raw OpenOCD instance.
    fn into_raw(self: Box<Self>) -> Result<OpenOcd>;
}

/// A trait which represents a TAP on a JTAG chain.
pub trait Jtag {
    // Stop further operation and returns raw OpenOCD instance.
    fn into_raw(self: Box<Self>) -> Result<OpenOcd>;

    // Returns the underlying OpenOCD instance.
    fn as_raw(&mut self) -> Result<&mut OpenOcd>;

    /// Disconnect from the TAP.
    fn disconnect(self: Box<Self>) -> Result<()>;
    /// Get TAP we are currently connected too.
    fn tap(&self) -> JtagTap;

    /// Read a lifecycle controller register.
    fn read_lc_ctrl_reg(&mut self, reg: &LcCtrlReg) -> Result<u32>;

    /// Write a value to a lifecycle controller register.
    fn write_lc_ctrl_reg(&mut self, reg: &LcCtrlReg, value: u32) -> Result<()>;

    /// Read bytes/words from memory into the provided buffer.
    /// When reading bytes, each memory access is 8 bits.
    /// When reading words, each memory access is 32 bit. If the hardware
    /// does not support unaligned memory accesses, this function will fail.
    ///
    /// On success, returns the number of bytes/words read.
    fn read_memory(&mut self, addr: u32, buf: &mut [u8]) -> Result<usize>;
    fn read_memory32(&mut self, addr: u32, buf: &mut [u32]) -> Result<usize>;

    /// Write bytes/words to memory.
    fn write_memory(&mut self, addr: u32, buf: &[u8]) -> Result<()>;
    fn write_memory32(&mut self, addr: u32, buf: &[u32]) -> Result<()>;

    /// Halt execution.
    fn halt(&mut self) -> Result<()>;

    /// Wait until the target halt. This does NOT halt the target on timeout.
    fn wait_halt(&mut self, timeout: Duration) -> Result<()>;

    /// Resume execution at its current code position.
    fn resume(&mut self) -> Result<()>;
    /// Resume execution at the specified address.
    fn resume_at(&mut self, addr: u32) -> Result<()>;

    /// Single-step the target at its current code position.
    fn step(&mut self) -> Result<()>;
    /// Single-step the target at the specified address.
    fn step_at(&mut self, addr: u32) -> Result<()>;

    /// Reset the target as hard as possible.
    /// If run is true, the target will start running code immediately
    /// after reset, otherwise it will be halted immediately.
    fn reset(&mut self, run: bool) -> Result<()>;

    /// Read/write a RISC-V register
    fn read_riscv_reg(&mut self, reg: &RiscvReg) -> Result<u32>;
    fn write_riscv_reg(&mut self, reg: &RiscvReg, val: u32) -> Result<()>;

    /// Set a breakpoint at the given address.
    fn set_breakpoint(&mut self, addr: u32, hw: bool) -> Result<()>;
    fn remove_breakpoint(&mut self, addr: u32) -> Result<()>;
    fn remove_all_breakpoints(&mut self) -> Result<()>;
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
#[derive(
    Clone,
    Copy,
    Debug,
    Deserialize,
    Serialize,
    strum::IntoStaticStr,
    strum::EnumIter,
    Eq,
    Hash,
    PartialEq,
)]
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
    PC,
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

    /// Get the address of this register
    pub fn addr(self) -> u16 {
        match self {
            Self::MSTATUS => 0x300,
            Self::MISA => 0x301,
            Self::MIE => 0x304,
            Self::MTVEC => 0x305,
            Self::MCOUNTINHIBIT => 0x320,
            Self::MHPMEVENT3 => 0x323,
            Self::MHPMEVENT4 => 0x324,
            Self::MHPMEVENT5 => 0x325,
            Self::MHPMEVENT6 => 0x326,
            Self::MHPMEVENT7 => 0x327,
            Self::MHPMEVENT8 => 0x328,
            Self::MHPMEVENT9 => 0x329,
            Self::MHPMEVENT10 => 0x32a,
            Self::MHPMEVENT11 => 0x32b,
            Self::MHPMEVENT12 => 0x32c,
            Self::MHPMEVENT13 => 0x32d,
            Self::MHPMEVENT14 => 0x32e,
            Self::MHPMEVENT15 => 0x32f,
            Self::MHPMEVENT16 => 0x330,
            Self::MHPMEVENT17 => 0x331,
            Self::MHPMEVENT18 => 0x332,
            Self::MHPMEVENT19 => 0x333,
            Self::MHPMEVENT20 => 0x334,
            Self::MHPMEVENT21 => 0x335,
            Self::MHPMEVENT22 => 0x336,
            Self::MHPMEVENT23 => 0x337,
            Self::MHPMEVENT24 => 0x338,
            Self::MHPMEVENT25 => 0x339,
            Self::MHPMEVENT26 => 0x33a,
            Self::MHPMEVENT27 => 0x33b,
            Self::MHPMEVENT28 => 0x33c,
            Self::MHPMEVENT29 => 0x33d,
            Self::MHPMEVENT30 => 0x33e,
            Self::MHPMEVENT31 => 0x33f,
            Self::MSCRATCH => 0x340,
            Self::MEPC => 0x341,
            Self::MCAUSE => 0x342,
            Self::MTVAL => 0x343,
            Self::MIP => 0x344,
            Self::PMPCFG0 => 0x3a0,
            Self::PMPCFG1 => 0x3a1,
            Self::PMPCFG2 => 0x3a2,
            Self::PMPCFG3 => 0x3a3,
            Self::PMPADDR0 => 0x3b0,
            Self::PMPADDR1 => 0x3b1,
            Self::PMPADDR2 => 0x3b2,
            Self::PMPADDR3 => 0x3b3,
            Self::PMPADDR4 => 0x3b4,
            Self::PMPADDR5 => 0x3b5,
            Self::PMPADDR6 => 0x3b6,
            Self::PMPADDR7 => 0x3b7,
            Self::PMPADDR8 => 0x3b8,
            Self::PMPADDR9 => 0x3b9,
            Self::PMPADDR10 => 0x3ba,
            Self::PMPADDR11 => 0x3bb,
            Self::PMPADDR12 => 0x3bc,
            Self::PMPADDR13 => 0x3bd,
            Self::PMPADDR14 => 0x3be,
            Self::PMPADDR15 => 0x3bf,
            Self::SCONTEXT => 0x5a8,
            Self::MSECCFG => 0x747,
            Self::MSECCFGH => 0x757,
            Self::TSELECT => 0x7a0,
            Self::TDATA1 => 0x7a1,
            Self::TDATA2 => 0x7a2,
            Self::TDATA3 => 0x7a3,
            Self::MCONTEXT => 0x7a8,
            Self::MSCONTEXT => 0x7aa,
            Self::DCSR => 0x7b0,
            Self::DPC => 0x7b1,
            Self::DSCRATCH0 => 0x7b2,
            Self::DSCRATCH1 => 0x7b3,
            Self::MCYCLE => 0xb00,
            Self::MINSTRET => 0xb02,
            Self::MHPMCOUNTER3 => 0xb03,
            Self::MHPMCOUNTER4 => 0xb04,
            Self::MHPMCOUNTER5 => 0xb05,
            Self::MHPMCOUNTER6 => 0xb06,
            Self::MHPMCOUNTER7 => 0xb07,
            Self::MHPMCOUNTER8 => 0xb08,
            Self::MHPMCOUNTER9 => 0xb09,
            Self::MHPMCOUNTER10 => 0xb0a,
            Self::MHPMCOUNTER11 => 0xb0b,
            Self::MHPMCOUNTER12 => 0xb0c,
            Self::MHPMCOUNTER13 => 0xb0d,
            Self::MHPMCOUNTER14 => 0xb0e,
            Self::MHPMCOUNTER15 => 0xb0f,
            Self::MHPMCOUNTER16 => 0xb10,
            Self::MHPMCOUNTER17 => 0xb11,
            Self::MHPMCOUNTER18 => 0xb12,
            Self::MHPMCOUNTER19 => 0xb13,
            Self::MHPMCOUNTER20 => 0xb14,
            Self::MHPMCOUNTER21 => 0xb15,
            Self::MHPMCOUNTER22 => 0xb16,
            Self::MHPMCOUNTER23 => 0xb17,
            Self::MHPMCOUNTER24 => 0xb18,
            Self::MHPMCOUNTER25 => 0xb19,
            Self::MHPMCOUNTER26 => 0xb1a,
            Self::MHPMCOUNTER27 => 0xb1b,
            Self::MHPMCOUNTER28 => 0xb1c,
            Self::MHPMCOUNTER29 => 0xb1d,
            Self::MHPMCOUNTER30 => 0xb1e,
            Self::MHPMCOUNTER31 => 0xb1f,
            Self::MCYCLEH => 0xb80,
            Self::MINSTRETH => 0xb82,
            Self::MHPMCOUNTER3H => 0xb83,
            Self::MHPMCOUNTER4H => 0xb84,
            Self::MHPMCOUNTER5H => 0xb85,
            Self::MHPMCOUNTER6H => 0xb86,
            Self::MHPMCOUNTER7H => 0xb87,
            Self::MHPMCOUNTER8H => 0xb88,
            Self::MHPMCOUNTER9H => 0xb89,
            Self::MHPMCOUNTER10H => 0xb8a,
            Self::MHPMCOUNTER11H => 0xb8b,
            Self::MHPMCOUNTER12H => 0xb8c,
            Self::MHPMCOUNTER13H => 0xb8d,
            Self::MHPMCOUNTER14H => 0xb8e,
            Self::MHPMCOUNTER15H => 0xb8f,
            Self::MHPMCOUNTER16H => 0xb90,
            Self::MHPMCOUNTER17H => 0xb91,
            Self::MHPMCOUNTER18H => 0xb92,
            Self::MHPMCOUNTER19H => 0xb93,
            Self::MHPMCOUNTER20H => 0xb94,
            Self::MHPMCOUNTER21H => 0xb95,
            Self::MHPMCOUNTER22H => 0xb96,
            Self::MHPMCOUNTER23H => 0xb97,
            Self::MHPMCOUNTER24H => 0xb98,
            Self::MHPMCOUNTER25H => 0xb99,
            Self::MHPMCOUNTER26H => 0xb9a,
            Self::MHPMCOUNTER27H => 0xb9b,
            Self::MHPMCOUNTER28H => 0xb9c,
            Self::MHPMCOUNTER29H => 0xb9d,
            Self::MHPMCOUNTER30H => 0xb9e,
            Self::MHPMCOUNTER31H => 0xb9f,
            Self::MVENDORID => 0xf11,
            Self::MARCHID => 0xf12,
            Self::MIMPID => 0xf13,
            Self::MHARTID => 0xf14,
            Self::CPUCTRL => todo!(),
            Self::SECURESEED => todo!(),
        }
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
