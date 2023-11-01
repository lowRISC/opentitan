// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::fs;
use std::ops::{Deref, DerefMut, Range};
use std::path::Path;
use std::time::Duration;

use anyhow::Result;
use object::{Object, ObjectSymbol};

use crate::io::jtag::{Jtag, RiscvCsr, RiscvGpr, RiscvReg};

pub struct ElfDebugger<'a> {
    symbols: HashMap<String, u32>,
    jtag: Box<dyn Jtag + 'a>,
}

impl<'a> Deref for ElfDebugger<'a> {
    type Target = dyn Jtag + 'a;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &*self.jtag
    }
}

impl<'a> DerefMut for ElfDebugger<'a> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.jtag()
    }
}

#[derive(Clone)]
pub enum SymbolicAddress {
    Absolute(u32),
    SymbolRelative(String, u32),
}

impl From<String> for SymbolicAddress {
    #[inline]
    fn from(s: String) -> Self {
        Self::SymbolRelative(s, 0)
    }
}

impl From<&str> for SymbolicAddress {
    #[inline]
    fn from(s: &str) -> Self {
        Self::SymbolRelative(s.to_owned(), 0)
    }
}

impl From<u32> for SymbolicAddress {
    #[inline]
    fn from(s: u32) -> Self {
        Self::Absolute(s)
    }
}

impl std::ops::Add<u32> for SymbolicAddress {
    type Output = Self;

    #[inline]
    fn add(self, rhs: u32) -> Self::Output {
        match self {
            SymbolicAddress::Absolute(addr) => SymbolicAddress::Absolute(addr + rhs),
            SymbolicAddress::SymbolRelative(symbol, offset) => {
                SymbolicAddress::SymbolRelative(symbol, offset + rhs)
            }
        }
    }
}

impl Debug for SymbolicAddress {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for SymbolicAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymbolicAddress::Absolute(addr) => write!(f, "{addr:#x}"),
            SymbolicAddress::SymbolRelative(symbol, offset) => {
                if *offset == 0 {
                    write!(f, "{symbol}")
                } else {
                    write!(f, "{symbol} + {offset:#x}")
                }
            }
        }
    }
}

#[derive(Clone)]
pub struct ResolvedAddress {
    pub address: SymbolicAddress,
    pub resolution: u32,
}

impl Debug for ResolvedAddress {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for ResolvedAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.address, f)?;

        // Only output the resolved address if it's not already absolute.
        if !matches!(self.address, SymbolicAddress::Absolute(_)) {
            write!(f, " ({:#x})", self.resolution)?;
        }

        Ok(())
    }
}

impl<'a> ElfDebugger<'a> {
    pub fn attach(jtag: Box<dyn Jtag + 'a>) -> Self {
        Self {
            symbols: HashMap::new(),
            jtag,
        }
    }

    pub fn load_elf(&mut self, path: impl AsRef<Path>) -> Result<()> {
        let elf_binary = fs::read(path)?;
        let elf_file = object::File::parse(&*elf_binary)?;
        for sym in elf_file.symbols() {
            self.symbols
                .insert(sym.name()?.to_owned(), sym.address() as u32);
        }
        Ok(())
    }

    pub fn disconnect(&mut self) -> Result<()> {
        self.jtag.disconnect()
    }

    /// Get the underlying JTAG interface.
    #[inline]
    pub fn jtag(&mut self) -> &mut (dyn Jtag + 'a) {
        &mut *self.jtag
    }

    /// Resolve a symbolic address.
    pub fn resolve(&self, address: impl Into<SymbolicAddress>) -> Result<ResolvedAddress> {
        let address = address.into();
        let resolution = match address {
            SymbolicAddress::Absolute(addr) => addr,
            SymbolicAddress::SymbolRelative(ref symbol, offset) => {
                let Some(symbol_addr) = self.symbols.get(symbol).copied() else {
                    anyhow::bail!("Cannot resolve symbol {symbol}");
                };
                symbol_addr + offset
            }
        };
        Ok(ResolvedAddress {
            address,
            resolution,
        })
    }

    /// Read a RISC-V register.
    ///
    /// This is a convience wrapper around `read_riscv_reg` provided by the JTAG trait.
    pub fn read_reg(&mut self, reg: impl Into<RiscvReg>) -> Result<u32> {
        self.read_riscv_reg(&reg.into())
    }

    /// Write a RISC-V register.
    ///
    /// This is a convience wrapper around `write_riscv_reg` provided by the JTAG trait.
    pub fn write_reg(&mut self, reg: impl Into<RiscvReg>, value: u32) -> Result<()> {
        self.write_riscv_reg(&reg.into(), value)
    }

    /// Read a 32-bit word from memory.
    ///
    /// This is a convience wrapper around `read_memory32` provided by the JTAG trait.
    pub fn read_u32(&mut self, addr: u32) -> Result<u32> {
        let mut ret = [0];
        self.read_memory32(addr, &mut ret)?;
        Ok(ret[0])
    }

    /// Write a 32-bit word to memory.
    ///
    /// This is a convience wrapper around `write_memory32` provided by the JTAG trait.
    pub fn write_u32(&mut self, addr: u32, value: u32) -> Result<()> {
        self.write_memory32(addr, &[value])
    }

    /// Read the program counter.
    pub fn get_pc(&mut self) -> Result<u32> {
        self.read_riscv_reg(&RiscvReg::Csr(RiscvCsr::DPC))
    }

    /// Set the program counter to the given address.
    pub fn set_pc(&mut self, address: impl Into<SymbolicAddress>) -> Result<()> {
        let resolved = self.resolve(address)?;
        log::info!("Set PC to {}", resolved);
        self.write_reg(RiscvCsr::DPC, resolved.resolution)?;
        Ok(())
    }

    /// Set a breakpoint at the given address.
    pub fn set_breakpoint(&mut self, address: impl Into<SymbolicAddress>) -> Result<()> {
        let resolved = self.resolve(address)?;
        log::info!("Set breakpoint at {}", resolved);
        self.jtag.set_breakpoint(resolved.resolution, true)?;
        Ok(())
    }

    /// Assert the current program counter is at the given address.
    pub fn expect_pc(&mut self, address: impl Into<SymbolicAddress>) -> Result<()> {
        let resolved = self.resolve(address)?;
        let pc = self.get_pc()?;
        log::info!("PC = {:#x}, expected PC = {}", pc, resolved);
        if pc != resolved.resolution {
            anyhow::bail!("unexpected PC");
        }
        Ok(())
    }

    /// Assert the current program counter is within the given range.
    pub fn expect_pc_range(&mut self, range: Range<impl Into<SymbolicAddress>>) -> Result<()> {
        let start = self.resolve(range.start)?;
        let end = self.resolve(range.end)?;
        let pc = self.get_pc()?;
        log::info!("PC = {:#x}, expected PC = {}..{}", pc, start, end,);
        if !(start.resolution..end.resolution).contains(&pc) {
            anyhow::bail!("unexpected PC");
        }
        Ok(())
    }

    /// Continue execution until the address is hit.
    ///
    /// Note that a breakpoint must not already exist for the target address, otherwise
    /// this function will fail.
    ///
    /// This function will also fail if a pre-existing breakpoint is hit before the target
    /// address is hit.
    pub fn run_until(
        &mut self,
        address: impl Into<SymbolicAddress>,
        timeout: Duration,
    ) -> Result<()> {
        let resolved = self.resolve(address)?;
        log::info!("Run until {}", resolved);
        self.jtag.set_breakpoint(resolved.resolution, true)?;
        self.jtag.resume()?;
        self.jtag.wait_halt(timeout)?;
        self.expect_pc(resolved.resolution)?;
        self.jtag.remove_breakpoint(resolved.resolution)?;
        Ok(())
    }

    /// Execute until the current function returns.
    ///
    /// This implementation does not use the debugging information from ELF files, and only uses the RA register,
    /// so it only works when RA has not been overriden, e.g. at the preamble of the function.
    pub fn finish(&mut self, timeout: Duration) -> Result<()> {
        let ra = self.read_reg(RiscvGpr::RA)?;
        self.run_until(ra, timeout)
    }

    /// Call a function with the given arguments.
    pub fn call(
        &mut self,
        address: impl Into<SymbolicAddress>,
        args: &[u32],
        timeout: Duration,
    ) -> Result<(u32, u32)> {
        // We're oblivious to the current context, so save all caller-saved registers.
        // In addition, also save SP, just in case that we have to modify it to align.
        const REGS_TO_SAVE: &[RiscvGpr] = &[
            RiscvGpr::RA,
            RiscvGpr::SP,
            RiscvGpr::T0,
            RiscvGpr::T1,
            RiscvGpr::T2,
            RiscvGpr::A0,
            RiscvGpr::A1,
            RiscvGpr::A2,
            RiscvGpr::A3,
            RiscvGpr::A4,
            RiscvGpr::A5,
            RiscvGpr::A6,
            RiscvGpr::A7,
            RiscvGpr::T3,
            RiscvGpr::T4,
            RiscvGpr::T5,
            RiscvGpr::T6,
        ];
        let mut saved = [0; REGS_TO_SAVE.len()];
        for (idx, gpr) in REGS_TO_SAVE.iter().copied().enumerate() {
            saved[idx] = self.read_reg(gpr)?;
        }

        // Align the stack if it's not currently 16-byte aligned.
        // This rounds down to avoid overwriting anything on stack.
        if saved[1] % 16 != 0 {
            self.write_reg(RiscvGpr::SP, saved[1] & !15)?;
        }

        // Set up arguments
        const ARG_GPRS: &[RiscvGpr] = &[
            RiscvGpr::A0,
            RiscvGpr::A1,
            RiscvGpr::A2,
            RiscvGpr::A3,
            RiscvGpr::A4,
            RiscvGpr::A5,
            RiscvGpr::A6,
        ];
        assert!(args.len() < ARG_GPRS.len());
        for (gpr, arg) in ARG_GPRS.iter().copied().zip(args.iter().copied()) {
            self.write_reg(gpr, arg)?;
        }

        // Set up call frame, and run until the current PC.
        // NOTE: This wouldn't guard against recursive function calls;
        // to support that we also need to check that SP is expected, but
        // this should be enough for all our current tests.
        let pc = self.get_pc()?;
        self.write_reg(RiscvGpr::RA, pc)?;
        self.set_pc(address)?;
        self.run_until(pc, timeout)?;

        // A0 and A1 serve as return value, read them.
        let a0 = self.read_reg(RiscvGpr::A0)?;
        let a1 = self.read_reg(RiscvGpr::A1)?;

        // Restore all registers
        for (idx, gpr) in REGS_TO_SAVE.iter().copied().enumerate() {
            self.write_reg(gpr, saved[idx])?;
        }

        Ok((a0, a1))
    }
}
