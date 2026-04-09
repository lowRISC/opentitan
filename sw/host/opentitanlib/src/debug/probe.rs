// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::jtag::{Jtag, JtagChain, JtagParams, JtagTap, RiscvGpr, RiscvReg};
use anyhow::{Result, bail, ensure};
use ot_hal::dif::lc_ctrl::LcCtrlReg;
use std::collections::HashMap;
use std::time::Duration;

use crate::debug::openocd::OpenOcd;
use probe_rs::probe::list::Lister;
use probe_rs::{CoreRegisters, MemoryInterface, Permissions, RegisterId, RegisterRole, Session};
use strum::IntoEnumIterator;

/// An JTAG interface driver over OpenOCD.
pub struct ProbeJtagChain {
    opts: JtagParams,
}

impl ProbeJtagChain {
    /// Prepare probe-rs backend with given JTAG options, but do not connect any TAP.
    #[allow(clippy::new_without_default)]
    pub fn new(opts: &JtagParams) -> ProbeJtagChain {
        ProbeJtagChain { opts: opts.clone() }
    }

    /// Converts a probe-rs core register list in to a mapping from the RiscvGpr type
    /// to the probe-rs RegisterId type
    fn generate_register_map(regs: &CoreRegisters) -> HashMap<RiscvGpr, RegisterId> {
        /*
            probe-rs uses register IDs to uniquely identify core registers (this is for all
            of the x0 to x31 registers, and the program counter.)
            These IDs have no clear pattern to them (they are not simply the numbers 0 to 31)
            Fortunately, we can get a list of registers from probe-rs after it connects to
            a chip. Unfortunately this list is in a very inconvenient format for looking up
            an ID value from the name of a register.

            To solve this problem, we build a mapping ahead of time, when the probe first connects
            to the chip, so that we can quickly look up the ID of any register we want to interract
            with.

            That is what this function does.
        */
        let mut reg_map = HashMap::new();
        for gpr in RiscvGpr::iter() {
            // Get the canonical name for each register known in the RiscvGpr enum
            let lname = gpr.name().to_lowercase();
            // Find a register with the same name in the data structure from probe-rs
            for r in regs.core_registers() {
                // Easy case: register name maps 1:1
                if r.name() == lname {
                    reg_map.insert(gpr, r.id());
                }
                // Trickier case: some registers have special roles, and these names are used instead.
                // For each of these cases, we find or generate the name, and check if it matches.
                for role in r.roles {
                    match role {
                        RegisterRole::Core(name)
                        | RegisterRole::Argument(name)
                        | RegisterRole::Return(name)
                        | RegisterRole::Other(name) => {
                            if *name == lname {
                                reg_map.insert(gpr, r.id());
                            }
                        }
                        RegisterRole::ReturnAddress => {
                            if lname == "ra" {
                                reg_map.insert(gpr, r.id());
                            }
                        }
                        RegisterRole::StackPointer => {
                            if lname == "sp" {
                                reg_map.insert(gpr, r.id());
                            }
                        }
                        RegisterRole::ProgramCounter => {
                            if lname == "pc" {
                                reg_map.insert(gpr, r.id());
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        reg_map
    }
}

impl JtagChain for ProbeJtagChain {
    fn into_raw(self: Box<Self>) -> Result<OpenOcd> {
        bail!("This is a probe-rs instance, unable to get a raw openocd instance")
    }

    fn connect(self: Box<Self>, tap: JtagTap) -> Result<Box<dyn Jtag>> {
        /*
          TODO currently will not connect to the lifecycle controller.
          the OOCD implementation does something like this to pick a config file for selecting the one:

            let target = match tap {
                JtagTap::RiscvTap => include_str!(env!("openocd_riscv_target_cfg")),
                JtagTap::LcTap => include_str!(env!("openocd_lc_target_cfg")),
            };

          eventually the probe-rs implementation should do something similar, and this will decide on what
          value to pass as the first argument to probe.attach().

          for more details see github issue: https://github.com/lowRISC/software-team/issues/37
        */
        if tap == JtagTap::LcTap {
            bail!(
                "connecting to the lifecycle controller is currently not supported when using probe-rs. Please use OpenOCD instead."
            )
        }

        // Get a list of all available debug probes.
        let lister = Lister::new();
        let probes = lister.list_all();

        // Select one of these probes to connect to
        let probe = if let Some(serial) = self.opts.jtag_usb_serial.as_ref() {
            // User has specified a probe to use, look for it in the list
            let mut probe = None;
            for p in probes {
                if p.serial_number.as_ref().is_some_and(|s| s == serial) {
                    if probe.is_some() {
                        // very unlikely, but this error case is handled
                        bail!(
                            "Multiple connected probes match the specified serial number: {}",
                            serial
                        );
                    }
                    probe = Some(p);
                }
            }
            if let Some(p) = probe {
                p.open()?
            } else {
                bail!("No probe found matching serial number: {}", serial)
            }
        } else {
            // The user has not specified a probe to use. If there is only one, use it, otherwise print a helpful error message
            ensure!(
                !probes.is_empty(),
                "No debug probes found when attempting to find any probe-rs compatible probes."
            );
            if probes.len() != 1 {
                let mut message = String::new();
                for p in probes {
                    message.push_str(&format!(
                        "\n{} (vid:pid=0x{:04x}:0x{:04x}, serial={})",
                        p.identifier,
                        p.vendor_id,
                        p.product_id,
                        p.serial_number
                            .unwrap_or("<unknown serial number>".to_string())
                    ));
                }
                bail!(
                    "Multiple debug probes found, please disconnect some probes, or specify a probe to use with --jtag-usb-serial=<serial_number>:{}",
                    message
                );
            }
            probes[0].open()?
        };

        // Attach to a chip.
        let mut session = probe.attach("earlgrey", Permissions::default())?;

        // Generate a lookup table to map register names to ID values
        let regs = session.core(0)?.registers();
        let reg_map = ProbeJtagChain::generate_register_map(regs);

        Ok(Box::new(ProbeJtagTap {
            jtag_tap: tap,
            session,
            reg_map,
        }))
    }
}

/// An JTAG interface driver over probe-rs.
pub struct ProbeJtagTap {
    /// JTAG TAP that Probe is connected to.
    jtag_tap: JtagTap,
    /// Contains the current probe-rs session
    session: Session,
    /// Stores a mapping of core register names to probe-rs register IDs
    reg_map: HashMap<RiscvGpr, RegisterId>,
}

impl ProbeJtagTap {
    fn reg_id(&self, reg: &RiscvGpr) -> Result<RegisterId> {
        let id = self.reg_map.get(reg);
        match id {
            None => {
                bail!(
                    "Unable to determine probe-rs register ID for register {:?}",
                    reg
                );
            }
            Some(id) => Ok(*id),
        }
    }
}

impl Jtag for ProbeJtagTap {
    fn into_raw(self: Box<Self>) -> Result<OpenOcd> {
        bail!("This is a probe-rs instance, unable to get a raw OpenOCD instance")
    }

    fn as_raw(&mut self) -> Result<&mut OpenOcd> {
        bail!("This is a probe-rs instance, unable to get a raw OpenOCD instance")
    }

    fn disconnect(self: Box<Self>) -> Result<()> {
        // Dropping the session instance will disconnect the probe from the tap
        // There is no need to actively do anything in this function, since Self
        // is passed by value, it will be dropped at the end of the function,
        // and the session also dropped as a result.
        Ok(())
    }

    fn tap(&self) -> JtagTap {
        self.jtag_tap
    }

    fn read_lc_ctrl_reg(&mut self, _reg: &LcCtrlReg) -> Result<u32> {
        todo!()
    }

    fn write_lc_ctrl_reg(&mut self, _reg: &LcCtrlReg, _value: u32) -> Result<()> {
        todo!()
    }

    fn read_memory(&mut self, addr: u32, buf: &mut [u8]) -> Result<usize> {
        let mut interface = self.session.get_riscv_interface(0)?;
        interface.read_8(addr as u64, buf)?;
        Ok(buf.len())
    }

    fn read_memory32(&mut self, addr: u32, buf: &mut [u32]) -> Result<usize> {
        let mut interface = self.session.get_riscv_interface(0)?;
        interface.read_32(addr as u64, buf)?;
        Ok(buf.len())
    }

    fn write_memory(&mut self, addr: u32, buf: &[u8]) -> Result<()> {
        let mut interface = self.session.get_riscv_interface(0)?;
        Ok(interface.write_8(addr as u64, buf)?)
    }

    fn write_memory32(&mut self, addr: u32, buf: &[u32]) -> Result<()> {
        let mut interface = self.session.get_riscv_interface(0)?;
        Ok(interface.write_32(addr as u64, buf)?)
    }

    fn halt(&mut self) -> Result<()> {
        self.session.core(0)?.halt(Duration::from_millis(10))?;
        Ok(())
    }

    fn wait_halt(&mut self, timeout: Duration) -> Result<()> {
        self.session.core(0)?.wait_for_core_halted(timeout)?;
        Ok(())
    }

    fn resume(&mut self) -> Result<()> {
        self.session.resume_all_cores()?;
        Ok(())
    }

    fn resume_at(&mut self, addr: u32) -> Result<()> {
        self.write_riscv_reg(&RiscvReg::Gpr(RiscvGpr::PC), addr)?;
        self.resume()?;
        Ok(())
    }

    fn reset(&mut self, _run: bool) -> Result<()> {
        self.session.core(0)?.reset()?;
        Ok(())
    }

    fn step(&mut self) -> Result<()> {
        self.session.core(0)?.step()?;
        Ok(())
    }

    fn step_at(&mut self, addr: u32) -> Result<()> {
        self.write_riscv_reg(&RiscvReg::Gpr(RiscvGpr::PC), addr)?;
        self.step()
    }

    fn read_riscv_reg(&mut self, reg: &RiscvReg) -> Result<u32> {
        match reg {
            RiscvReg::Gpr(reg) => {
                let id = self.reg_id(reg)?;
                Ok(self.session.core(0)?.read_core_reg(id)?)
            }
            RiscvReg::Csr(reg) => {
                let mut interface = self.session.get_riscv_interface(0)?;
                Ok(interface.read_csr_progbuf(reg.addr())?)
            }
        }
    }

    fn write_riscv_reg(&mut self, reg: &RiscvReg, val: u32) -> Result<()> {
        match reg {
            RiscvReg::Gpr(reg) => {
                let id = self.reg_id(reg)?;
                Ok(self.session.core(0)?.write_core_reg(id, val)?)
            }
            RiscvReg::Csr(reg) => {
                let mut interface = self.session.get_riscv_interface(0)?;
                Ok(interface.write_csr_progbuf(reg.addr(), val)?)
            }
        }
    }

    fn set_breakpoint(&mut self, address: u32, hw: bool) -> Result<()> {
        if hw {
            self.session.core(0)?.set_hw_breakpoint(address as u64)?;
        } else {
            todo!()
        }
        Ok(())
    }

    fn remove_breakpoint(&mut self, addr: u32) -> Result<()> {
        self.session.core(0)?.clear_hw_breakpoint(addr as u64)?;
        Ok(())
    }

    fn remove_all_breakpoints(&mut self) -> Result<()> {
        // NOTE: this is likely to hang the program when called
        self.session.core(0)?.clear_all_hw_breakpoints()?;
        Ok(())
    }
}
