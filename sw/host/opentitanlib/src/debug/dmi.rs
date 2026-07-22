// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::ops::{Deref, DerefMut};
use std::time::Duration;

use anyhow::{Context, Result, bail, ensure};
use thiserror::Error;

use super::openocd::OpenOcd;
use crate::test_utils::poll::poll_until;

/// Constants defined by RISC-V Debug Specification 0.13.
pub mod consts {
    // JTAG registers.
    pub const DTMCS: u32 = 0x10;
    pub const DMI: u32 = 0x11;

    pub const DTMCS_VERSION_SHIFT: u32 = 0;
    pub const DTMCS_ABITS_SHIFT: u32 = 4;
    pub const DTMCS_IDLE_SHIFT: u32 = 12;
    pub const DTMCS_DMIRESET_SHIFT: u32 = 16;

    pub const DTMCS_VERSION_MASK: u32 = 0xf << DTMCS_VERSION_SHIFT;
    pub const DTMCS_ABITS_MASK: u32 = 0x3f << DTMCS_ABITS_SHIFT;
    pub const DTMCS_IDLE_MASK: u32 = 0x7 << DTMCS_IDLE_SHIFT;
    pub const DTMCS_DMIRESET_MASK: u32 = 1 << DTMCS_DMIRESET_SHIFT;

    pub const DTMCS_VERSION_0_13: u32 = 1;

    pub const DMI_ADDRESS_SHIFT: u32 = 34;
    pub const DMI_DATA_SHIFT: u32 = 2;

    pub const DMI_OP_READ: u64 = 0x1;
    pub const DMI_OP_WRITE: u64 = 0x2;

    // Debug module registers.
    pub const DATA0: u32 = 0x04;
    pub const DATA1: u32 = 0x05;
    pub const DMCONTROL: u32 = 0x10;
    pub const DMSTATUS: u32 = 0x11;
    pub const HARTINFO: u32 = 0x12;
    pub const ABSTRACTCS: u32 = 0x16;

    pub const DMSTATUS_ANYHALTED_MASK: u32 = 1 << 8;
    pub const DMSTATUS_ANYRUNNING_MASK: u32 = 1 << 10;
    pub const DMSTATUS_ANYUNAVAIL_MASK: u32 = 1 << 12;
    pub const DMSTATUS_ANYNONEXISTENT_MASK: u32 = 1 << 14;
    pub const DMSTATUS_ANYRESUMEACK_MASK: u32 = 1 << 16;
    pub const DMSTATUS_ANYHAVERESET_MASK: u32 = 1 << 18;
    pub const DMSTATUS_ALLHAVERESET_MASK: u32 = 1 << 19;

    pub const DMCONTROL_HASEL_SHIFT: u32 = 26;
    pub const DMCONTROL_HARTSELHI_SHIFT: u32 = 6;
    pub const DMCONTROL_HARTSELLO_SHIFT: u32 = 16;

    pub const DMCONTROL_DMACTIVE_MASK: u32 = 1 << 0;
    pub const DMCONTROL_NDMRESET_MASK: u32 = 1 << 1;
    pub const DMCONTROL_ACKHAVERESET_MASK: u32 = 1 << 28;
    pub const DMCONTROL_RESUMEREQ_MASK: u32 = 1 << 30;
    pub const DMCONTROL_HALTREQ_MASK: u32 = 1 << 31;

    pub const ABSTRACTCS_CMDERR_MASK: u32 = (1 << 11) - (1 << 8);
    pub const ABSTRACTCS_BUSY_MASK: u32 = 1 << 12;

    pub const ABSTRACTCS_CMDERR_SHIFT: u32 = 8;

    pub const ABSTRACTCS_CMDERR_NONE: u32 = 0;
}

use consts::*;

/// Debug module interface (DMI) abstraction.
pub trait Dmi {
    /// Read a DMI register.
    fn dmi_read(&mut self, addr: u32) -> Result<u32>;

    /// Write a DMI register.
    fn dmi_write(&mut self, addr: u32, data: u32) -> Result<()>;

    /// Perform a batch of sequential writes to DMI registers.
    /// May or may not be more optimized depending on the underlying implementation.
    fn batched_dmi_writes(&mut self, writes: &[(u32, u32)]) -> Result<()> {
        writes
            .iter()
            .try_for_each(|&(addr, data)| self.dmi_write(addr, data))
    }

    /// Perform a batch of sequential reads from DMI registers, returning the read values
    /// in the same order as the given addresses.
    /// May or may not be more optimized depending on the underlying implementation.
    fn batched_dmi_reads(&mut self, addrs: &[u32]) -> Result<Vec<u32>> {
        addrs.iter().map(|&addr| self.dmi_read(addr)).collect()
    }
}

impl<T: Dmi> Dmi for &mut T {
    fn dmi_read(&mut self, addr: u32) -> Result<u32> {
        T::dmi_read(self, addr)
    }

    fn dmi_write(&mut self, addr: u32, data: u32) -> Result<()> {
        T::dmi_write(self, addr, data)
    }

    fn batched_dmi_writes(&mut self, writes: &[(u32, u32)]) -> Result<()> {
        T::batched_dmi_writes(self, writes)
    }

    fn batched_dmi_reads(&mut self, addrs: &[u32]) -> Result<Vec<u32>> {
        T::batched_dmi_reads(self, addrs)
    }
}

/// DMI interface via OpenOCD.
pub struct OpenOcdDmi {
    openocd: OpenOcd,
    tap: String,
    abits: u32,
    /// Extra `runtest` cycles to insert after a DMI scan, on top of the 1 cycle in
    /// Run-Test/Idle that every scan already ends in by default.
    extra_idle: u32,
}

/// Extra `runtest` cycles per DMI scan used unless overridden by `OT_DMI_EXTRA_IDLE`.
const DEFAULT_EXTRA_IDLE: u32 = 3;

impl OpenOcdDmi {
    /// Create a new DMI interface via OpenOCD.
    ///
    /// This should be an OpenOCD instance with JTAG scan chain already set up,
    /// but not with target set up. If target has been set up, OpenOCD will access
    /// DMI registers on its own, which will interfere with raw DMI operations.
    pub fn new(mut openocd: OpenOcd, tap: &str) -> Result<Self> {
        let target_names = openocd.execute("target names")?;
        ensure!(
            target_names.is_empty(),
            "Target must not be setup when accessing DMI directly"
        );

        openocd.irscan(tap, DTMCS)?;
        let res = openocd.drscan(tap, 32, DTMCS_DMIRESET_MASK)?;
        let version = (res & DTMCS_VERSION_MASK) >> DTMCS_VERSION_SHIFT;
        let abits = (res & DTMCS_ABITS_MASK) >> DTMCS_ABITS_SHIFT;
        let idle = (res & DTMCS_IDLE_MASK) >> DTMCS_IDLE_SHIFT;

        ensure!(
            version == DTMCS_VERSION_0_13,
            "DTMCS indicates version other than 0.13"
        );

        let extra_idle = match std::env::var("OT_DMI_EXTRA_IDLE") {
            Ok(val) => val.parse().context("invalid OT_DMI_EXTRA_IDLE")?,
            Err(_) => DEFAULT_EXTRA_IDLE,
        };
        log::info!(
            "DTMCS.idle = {idle} (using {extra_idle} extra runtest cycle(s) per scan; \
             set OT_DMI_EXTRA_IDLE to override)"
        );

        openocd.irscan(tap, DMI)?;
        Ok(Self {
            openocd,
            tap: tap.to_owned(),
            abits,
            extra_idle,
        })
    }

    fn drscan_bits(&self) -> u32 {
        self.abits + DMI_ADDRESS_SHIFT
    }

    /// Wait for `extra_idle` cycles in Run-Test/Idle, if the DTM needs more than the one cycle
    /// every scan already ends in.
    fn wait_idle(&mut self) -> Result<()> {
        if self.extra_idle > 0 {
            self.openocd
                .execute(&format!("runtest {}", self.extra_idle))?;
        }
        Ok(())
    }

    fn dmi_op(&mut self, op: u64) -> Result<u64> {
        let res = self.openocd.drscan(&self.tap, self.drscan_bits(), op)?;

        // We just scanned into the DMI register, so the scanned result should be empty.
        ensure!(res == 0, "Unexpected DMI initial response {res:#x}");

        // Give the DTM the idle time it asked for to service the operation.
        self.wait_idle()?;

        // Read the result.
        let res = self.openocd.drscan(&self.tap, self.drscan_bits(), 0)?;
        ensure!(res & 3 == 0, "DMI operation failed with {res:#x}");

        // Double check the address matches.
        ensure!(
            res >> DMI_ADDRESS_SHIFT == op >> DMI_ADDRESS_SHIFT,
            "DMI operation address mismatch {res:#x}"
        );

        Ok(res)
    }
}

impl Dmi for OpenOcdDmi {
    fn dmi_read(&mut self, addr: u32) -> Result<u32> {
        let output = (self.dmi_op((addr as u64) << DMI_ADDRESS_SHIFT | DMI_OP_READ)?
            >> DMI_DATA_SHIFT) as u32;
        log::debug!("DMI read {:#x} -> {:#x}", addr, output);
        Ok(output)
    }

    fn dmi_write(&mut self, addr: u32, value: u32) -> Result<()> {
        self.dmi_op(
            (addr as u64) << DMI_ADDRESS_SHIFT | (value as u64) << DMI_DATA_SHIFT | DMI_OP_WRITE,
        )?;
        log::debug!("DMI write {:#x} <- {:#x}", addr, value);
        Ok(())
    }

    fn batched_dmi_writes(&mut self, writes: &[(u32, u32)]) -> Result<()> {
        if writes.is_empty() {
            return Ok(());
        }

        log::debug!(
            "DMI {} batched writes: {}",
            writes.len(),
            writes
                .iter()
                .map(|&(addr, value)| format!("{:#x} <- {:#x}", addr, value))
                .collect::<Vec<_>>()
                .join(", ")
        );

        // Chunk the batch to stay well under OpenOCD's ~4 MiB TCL RPC command buffer
        const CHUNK_SIZE: usize = 512;

        for chunk in writes.chunks(CHUNK_SIZE) {
            // For optimized writes via drscan, we perform direct drscan write operations,
            // waiting in the RunTest state after each one (per `DTMCS.idle`, see `wait_idle`)
            // so the DTM has time to service it before the next write lands. We only check the
            // returned scanned values at the end of each chunk, with a final write to check the
            // scan status (as errors are sticky).
            let mut cmd = chunk
                .iter()
                .map(|&(addr, value)| {
                    let data = (addr as u64) << DMI_ADDRESS_SHIFT
                        | (value as u64) << DMI_DATA_SHIFT
                        | DMI_OP_WRITE;
                    let scan = self.openocd.drscan_cmd(&self.tap, self.drscan_bits(), data);
                    if self.extra_idle > 0 {
                        format!("{scan}\nruntest {}", self.extra_idle)
                    } else {
                        scan
                    }
                })
                .collect::<Vec<_>>()
                .join("\n");
            cmd.push_str(
                format!(
                    "\n{}",
                    self.openocd.drscan_cmd(&self.tap, self.drscan_bits(), 0)
                )
                .as_str(),
            );
            let result = self.openocd.execute(&cmd)?;

            // The final NOP scan's captured value carries the DMI status of this chunk:
            // failed or dropped-while-busy operations leave a sticky nonzero op field, so a
            // clean status here means every write in the chunk was accepted.
            let res = u64::from_str_radix(result.trim(), 16)
                .with_context(|| format!("unexpected DMI batched write response '{result}'"))?;
            ensure!(
                res & 3 == 0,
                "DMI batched write failed with sticky status {res:#x}; at least one write was \
                 dropped (is the JTAG clock too fast for the DMI to keep up?)"
            );
        }
        Ok(())
    }

    fn batched_dmi_reads(&mut self, addrs: &[u32]) -> Result<Vec<u32>> {
        // Pipelined DMI reads: each `drscan` shifts in the next read operation while shifting
        // out the response of the previous one, so a chunk of N reads costs a single TCL round
        // trip instead of 3 round trips per read via `dmi_read`. Operations execute strictly in
        // order at the DTM.
        const CHUNK_SIZE: usize = 512;

        let mut values = Vec::with_capacity(addrs.len());
        for chunk in addrs.chunks(CHUNK_SIZE) {
            let mut cmd = String::from("set _r {}");
            for &addr in chunk {
                let op = (addr as u64) << DMI_ADDRESS_SHIFT | DMI_OP_READ;
                cmd.push_str(&format!(
                    "\nlappend _r [{}]",
                    self.openocd.drscan_cmd(&self.tap, self.drscan_bits(), op)
                ));
                if self.extra_idle > 0 {
                    cmd.push_str(&format!("\nruntest {}", self.extra_idle));
                }
            }
            // A trailing NOP scan collects the final read's response.
            cmd.push_str(&format!(
                "\nlappend _r [{}]\nset _r",
                self.openocd.drscan_cmd(&self.tap, self.drscan_bits(), 0)
            ));

            let result = self.openocd.execute(&cmd)?;
            let entries = result
                .split_whitespace()
                .map(|s| {
                    u64::from_str_radix(s, 16)
                        .with_context(|| format!("unexpected DMI batched read response '{s}'"))
                })
                .collect::<Result<Vec<u64>>>()?;
            ensure!(
                entries.len() == chunk.len() + 1,
                "DMI batched read returned {} entries, expected {}",
                entries.len(),
                chunk.len() + 1
            );

            // Entry k is captured while scanning in operation k and holds the response of
            // operation k-1: entry 0 belongs to whatever preceded this chunk (only its status
            // matters), entries 1..=N are the responses of this chunk's reads, in order.
            for (idx, &res) in entries.iter().enumerate() {
                ensure!(
                    res & 3 == 0,
                    "DMI batched read failed with sticky status {res:#x} at entry {idx} \
                     (is the JTAG clock too fast for the DMI to keep up?)"
                );
                if idx > 0 {
                    let addr = chunk[idx - 1];
                    ensure!(
                        res >> DMI_ADDRESS_SHIFT == addr as u64,
                        "DMI batched read address mismatch: expected {addr:#x}, response {res:#x}"
                    );
                    values.push((res >> DMI_DATA_SHIFT) as u32);
                }
            }
        }

        Ok(values)
    }
}

#[derive(Debug, Error)]
pub enum DmiError {
    #[error("Hart does not exist")]
    Nonexistent,
    #[error("Hart is not currently available")]
    Unavailable,
    #[error("Timeout waiting for hart to halt")]
    WaitTimeout,
}

/// A debugger that communicates with the target via RISC-V Debug Module Interface (DMI).
pub struct DmiDebugger<D> {
    dmi: D,
    hartsel_mask: Option<u32>,
}

impl<D> Deref for DmiDebugger<D> {
    type Target = D;

    fn deref(&self) -> &Self::Target {
        &self.dmi
    }
}

impl<D> DerefMut for DmiDebugger<D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.dmi
    }
}

impl<D: Dmi> DmiDebugger<D> {
    pub fn new(dmi: D) -> Self {
        Self {
            dmi,
            hartsel_mask: None,
        }
    }

    /// Obtain bits valid in hartsel as a bitmask.
    pub fn hartsel_mask(&mut self) -> Result<u32> {
        if self.hartsel_mask.is_none() {
            // Write all 1s to hartsel.
            let dm_control = 0 << DMCONTROL_HASEL_SHIFT
                | 0x3ff << DMCONTROL_HARTSELLO_SHIFT
                | 0x3ff << DMCONTROL_HARTSELHI_SHIFT
                | DMCONTROL_DMACTIVE_MASK;
            self.dmi.dmi_write(DMCONTROL, dm_control)?;

            // This is a WARL register so after writing 1, the readback value would be
            // the mask for valid bits in the register.
            let dm_control = self.dmi.dmi_read(DMCONTROL)?;
            let hart_select = (dm_control >> DMCONTROL_HARTSELLO_SHIFT) & 0x3ff
                | ((dm_control >> DMCONTROL_HARTSELHI_SHIFT) & 0x3ff) << 10;

            self.hartsel_mask = Some(hart_select);
        }

        Ok(self.hartsel_mask.unwrap())
    }

    /// Selects a hart to debug.
    pub fn select_hart(&mut self, hartid: u32) -> Result<DmiHart<'_, D>> {
        // The hart selection is up to 20 bits.
        if hartid >= (1 << 20) {
            bail!("Invalid hartid: {hartid}");
        }

        // When selecting non-zero hart, ensure written bit to HARTSEL is legal.
        if hartid != 0 {
            let mask = self.hartsel_mask()?;
            if (hartid & mask) != hartid {
                bail!(DmiError::Nonexistent);
            }
        }

        let hart_select = 0 << DMCONTROL_HASEL_SHIFT
            | (hartid & 0x3ff) << DMCONTROL_HARTSELLO_SHIFT
            | (hartid >> 10) << DMCONTROL_HARTSELHI_SHIFT
            | DMCONTROL_DMACTIVE_MASK;
        self.dmi.dmi_write(DMCONTROL, hart_select)?;

        let mut hart = DmiHart {
            debugger: self,
            hart_select,
        };

        let dmstatus = hart.dmstatus()?;
        if dmstatus & DMSTATUS_ANYNONEXISTENT_MASK != 0 {
            bail!(DmiError::Nonexistent);
        }
        if dmstatus & DMSTATUS_ANYUNAVAIL_MASK != 0 {
            bail!(DmiError::Unavailable);
        }

        Ok(hart)
    }

    /// Read a data register from DMI.
    pub fn data(&mut self, idx: u32) -> Result<u32> {
        ensure!(idx < 12, "data register index out of range {:#x}", idx);
        self.dmi_read(DATA0 + idx)
    }

    /// Write a data register from DMI.
    pub fn set_data(&mut self, idx: u32, data: u32) -> Result<()> {
        ensure!(idx < 12, "data register index out of range {:#x}", idx);
        self.dmi_write(DATA0 + idx, data)
    }
}

/// A DMI debugger with specific hart selected.
pub struct DmiHart<'a, D> {
    debugger: &'a mut DmiDebugger<D>,

    /// The value of DMCONTROL with hasel, hartsello and hartselhi set.
    hart_select: u32,
}

impl<D> Deref for DmiHart<'_, D> {
    type Target = DmiDebugger<D>;

    fn deref(&self) -> &Self::Target {
        self.debugger
    }
}

impl<D> DerefMut for DmiHart<'_, D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.debugger
    }
}

/// State of the hart.
///
/// If both `running` and `halted` are false, then the hart is in the process of transitioning between
/// the two states (i.e. resuming or halting).
pub struct HartState {
    pub running: bool,
    pub halted: bool,
}

impl<D: Dmi> DmiHart<'_, D> {
    /// Read `dmstatus` for the selected hart.
    pub fn dmstatus(&mut self) -> Result<u32> {
        let dmstatus = self.debugger.dmi_read(DMSTATUS)?;

        // `dmstatus` register have fields for any hart and all harts. If only a single hart is selected,
        // then the "all" and "any" values should match. This performs a sanity check.
        if (dmstatus ^ (dmstatus >> 1))
            & (DMSTATUS_ANYHALTED_MASK
                | DMSTATUS_ANYRUNNING_MASK
                | DMSTATUS_ANYUNAVAIL_MASK
                | DMSTATUS_ANYNONEXISTENT_MASK
                | DMSTATUS_ANYRESUMEACK_MASK
                | DMSTATUS_ANYHAVERESET_MASK)
            != 0
        {
            bail!(
                "Invalid dmstatus {:#x}: any and all bits mismatch",
                dmstatus
            );
        }

        Ok(dmstatus)
    }

    /// Write to dmcontrol without affecting hart selection.
    pub fn set_dmcontrol(&mut self, value: u32) -> Result<()> {
        self.debugger.dmi_write(DMCONTROL, value | self.hart_select)
    }

    /// Read hart info of the selected hart.
    pub fn hartinfo(&mut self) -> Result<u32> {
        self.debugger.dmi_read(HARTINFO)
    }

    /// Return the state of the hart.
    pub fn state(&mut self) -> Result<HartState> {
        let dmstatus = self.dmstatus()?;
        let running = dmstatus & DMSTATUS_ANYRUNNING_MASK != 0;
        let halted = dmstatus & DMSTATUS_ANYHALTED_MASK != 0;
        assert!(!(running && halted));
        Ok(HartState { running, halted })
    }

    /// Set the halt request bit.
    pub fn set_halt_request(&mut self, active: bool) -> Result<()> {
        self.set_dmcontrol(if active { DMCONTROL_HALTREQ_MASK } else { 0 })
    }

    /// Wait for the hart to halt.
    pub fn wait_halt(&mut self) -> Result<()> {
        // Per RISC-V debug specification, harts must respond within 1 second of receiving a halt or
        // resume request.
        poll_until(Duration::from_secs(1), Duration::from_millis(50), || {
            Ok(self.state()?.halted)
        })
    }

    /// Set the resume request bit.
    pub fn set_resume_request(&mut self, active: bool) -> Result<()> {
        self.set_dmcontrol(if active { DMCONTROL_RESUMEREQ_MASK } else { 0 })
    }

    /// Wait for the hart to resume.
    pub fn wait_resume(&mut self) -> Result<()> {
        // Per RISC-V debug specification, harts must respond within 1 second of receiving a halt or
        // resume request.
        poll_until(Duration::from_secs(1), Duration::from_secs(1), || {
            Ok(self.state()?.running)
        })
    }
}
