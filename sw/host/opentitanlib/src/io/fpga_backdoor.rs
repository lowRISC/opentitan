// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use clap::Args;
use serde::ser::{Serialize, SerializeStruct, Serializer};
use std::time::Duration;

use crate::app::TransportWrapper;
use crate::debug::dmi::{Dmi, OpenOcdDmi};
use crate::io::jtag::{JtagChain, JtagParams, JtagTap};
use crate::transport::Capability;

/// FPGA Backdoor loader register offsets (byte-addressed) and field definitions.
/// See hw/ip/bkdr_loader/doc/registers.md
/// TODO: it would be nice to use Bazel to auto-generate a rust "header" for this IP instead.
pub mod regs {

    // STATUS register
    pub const STATUS_REG_OFFSET: usize = 0x0;
    pub const STATUS_ERROR_BIT: u32 = 0;

    // CONTROL register
    pub const CONTROL_REG_OFFSET: usize = 0x4;
    pub const CONTROL_DONE_BIT: u32 = 0;
    pub const CONTROL_WRITE_ENA_BIT: u32 = 1;
    pub const CONTROL_TARGET_IDX_MASK: u32 = 0xff;
    pub const CONTROL_TARGET_IDX_OFFSET: usize = 8;

    // Other registers (all have one 32-bit `VAL` field)
    pub const NUM_BKDR_TARGETS_REG_OFFSET: usize = 0x8;
    pub const MISSION_MODE_SWITCH_DELAY_REG_OFFSET: usize = 0xc;
    pub const USR_ACCESS_TIMESTAMP_REG_OFFSET: usize = 0x10;
    pub const TARGET_INFO_0_REG_OFFSET: usize = 0x100;
    pub const WIDTH_INFO_0_REG_OFFSET: usize = 0x200;
    pub const DEPTH_INFO_0_REG_OFFSET: usize = 0x300;
    pub const READ_DATA_0_REG_OFFSET: usize = 0x400;
    pub const WRITE_DATA_0_REG_OFFSET: usize = 0x500;
    pub const INDEX_REG_OFFSET: usize = 0x600;
}

pub mod consts {
    // How long the reset strapping is applied for when entering the backdoor loader.
    pub const RESET_PULSE_MS: u64 = 50;

    // How long the backdoor loader TAP strapping is held after leaving reset.
    pub const HOLD_TAP_STRAPS_MS: u64 = 50;

    // How many JTAG cycles to wait for before considering the `CONTROL.DONE` transaction
    // as being completed. We default to 10000, which is a conservative threshold.
    pub const JTAG_DONE_CYCLES: u64 = 10000;

    // FIXME: This should be refactored so that the ot_transport JSON5 file declares clock
    // frequencies for each device which we can then query through the transport. This
    // is hardcoded for now for convenience.
    pub const CW340_MAIN_CLOCK_FREQ_HZ: u64 = 24 * 1000 * 1000; // 24 MHz

    // Parameters - see hw/ip/bkdr_loader/doc/interfaces.md
    pub const DATA_REGS_PER_WORD: usize = 8; // MaxWordWidthDiv32
}

use consts::*;

/// Apply the bkdr_loader TAP strapping and reset to enter the backdoor loader.
pub fn enter_backdoor_loader(transport: &TransportWrapper) -> Result<()> {
    transport.capabilities()?.request(Capability::GPIO).ok()?;
    let pinmux_tap_backdoor = transport.pin_strapping("PINMUX_TAP_FPGA_BACKDOOR")?;
    let reset = transport.pin_strapping("RESET")?;

    pinmux_tap_backdoor.apply()?;
    reset.apply()?;
    std::thread::sleep(Duration::from_millis(RESET_PULSE_MS));
    reset.remove()?;
    std::thread::sleep(Duration::from_millis(HOLD_TAP_STRAPS_MS));
    pinmux_tap_backdoor.remove()
}

/// A struct which represents a backdoor loader interface.
///
/// This struct represents an adaptor that has been configured to connect to a given JTAG chain,
/// but has not yet been configured to access the backdoor TAP.
pub struct BackdoorTap<'a> {
    jtag: Box<dyn JtagChain + 'a>,
    jtag_speed_khz: u64,
}

impl BackdoorTap<'_> {
    /// Connect to the backdoor TAP, optionally enumerate information about all targets.
    pub fn connect(self, enumerate: bool) -> Result<Backdoor> {
        let openocd = self.jtag.connect(JtagTap::BackdoorTap)?.into_raw()?;
        Backdoor::new(
            OpenOcdDmi::new(openocd, "fpga_backdoor.tap")?,
            self.jtag_speed_khz,
            enumerate,
        )
    }
}

#[derive(Debug, Args, Clone)]
pub struct BackdoorParams {
    /// JTAG options to apply to the backdoor TAP.
    #[command(flatten)]
    jtag: JtagParams,
}

impl BackdoorParams {
    pub fn create<'a>(&self, transport: &'a TransportWrapper) -> Result<BackdoorTap<'a>> {
        Ok(BackdoorTap {
            jtag: self.jtag.create(transport)?,
            jtag_speed_khz: self.jtag.adapter_speed_khz,
        })
    }
}

/// Information about a specific backdoor target, e.g. OTP, ROM, FB0, SRAM.
#[derive(Debug, Clone, Copy)]
pub struct BackdoorTargetInfo {
    /// The unique identifier of the backdoor target
    pub id: u32,
    /// The word width of the memory of the backdoor target.
    pub width: u32,
    /// The depth (number of words) of the memory of the backdoor target.
    pub depth: u32,
}

impl BackdoorTargetInfo {
    /// The target's unique identifier as a <= 4 character UTF-8 string.
    pub fn id_str(&self) -> String {
        let bytes = self.id.to_be_bytes();

        String::from_utf8_lossy(&bytes).trim_end().to_owned()
    }

    // Convert a UTF-8 ID string into the unique u32 identifier format used by targets.
    pub fn id_from_str(id: &str) -> Result<u32> {
        let mut bytes = [32u8; 4];
        let src = id.as_bytes();
        let len = id.len().min(4);
        bytes[..len].copy_from_slice(&src[..len]);

        Ok(u32::from_be_bytes(bytes))
    }
}

impl Serialize for BackdoorTargetInfo {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_struct("BackdoorTargetInfo", 4)?;
        s.serialize_field("id", &self.id)?;
        s.serialize_field("id_str", &self.id_str())?;
        s.serialize_field("width", &self.width)?;
        s.serialize_field("depth", &self.depth)?;
        s.end()
    }
}

impl std::fmt::Display for BackdoorTargetInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} {} x {}", self.id_str(), self.width, self.depth)
    }
}

/// Handle for interacting with a given target via the backdoor loader.
pub struct BackdoorTarget {
    /// Information about the target.
    pub info: BackdoorTargetInfo,
}

/// A struct which represents an active backdoor loader connection.
pub struct Backdoor {
    dmi: OpenOcdDmi,
    jtag_speed_khz: u64,
    targets: Vec<BackdoorTargetInfo>,
}

impl Backdoor {
    /// Construct a [`Backdoor`] from a DMI connection to the backdoor TAP. Optionally
    /// enumerate and discover information about all available targets.
    pub fn new(dmi: OpenOcdDmi, jtag_speed_khz: u64, enumerate: bool) -> Result<Self> {
        let mut fpga_backdoor = Self {
            dmi,
            jtag_speed_khz,
            targets: Vec::new(),
        };
        if enumerate {
            fpga_backdoor.enumerate()?;
        }

        Ok(fpga_backdoor)
    }

    /// Read from a DMI register with the given byte address offset.
    /// DMI is a register interface; we must map the byte offsets to register (word) index.
    fn dmi_read(&mut self, byte_addr: usize) -> Result<u32> {
        self.dmi.dmi_read(byte_addr as u32 >> 2)
    }

    /// Write a value to a DMI register with the given byte address offset.
    /// DMI is a register interface; we must map the byte offsets to register (word) index.
    fn dmi_write(&mut self, byte_addr: usize, data: u32) -> Result<()> {
        self.dmi.dmi_write(byte_addr as u32 >> 2, data)
    }

    // Enumerate the backdoor loader and retrieve information about available targets.
    pub fn enumerate(&mut self) -> Result<()> {
        self.targets.clear();

        let num_targets = self
            .dmi_read(regs::NUM_BKDR_TARGETS_REG_OFFSET)
            .context("cannot read number of targets")? as usize;
        log::info!("Number of FPGA bkdr_loader targets: {num_targets:?}");
        for idx in 0..num_targets {
            let addr_offset = idx * 4;
            let target_info = BackdoorTargetInfo {
                id: self
                    .dmi_read(regs::TARGET_INFO_0_REG_OFFSET + addr_offset)
                    .context("cannot read target info")?,
                width: self
                    .dmi_read(regs::WIDTH_INFO_0_REG_OFFSET + addr_offset)
                    .context("cannot read width info")?,
                depth: self
                    .dmi_read(regs::DEPTH_INFO_0_REG_OFFSET + addr_offset)
                    .context("cannot read depth info")?,
            };
            self.targets.push(target_info);
        }

        Ok(())
    }

    /// Communicate with the backdoor loader that we are finished using it.
    ///
    /// This transitions the bkdr_loader from it from its "Preload" state to "Mission mode",
    /// causing it to re-route incoming JTAG back to the regular downstream interface.
    pub fn set_done(mut self) -> Result<()> {
        log::debug!("Finished using backdoor loader until next reset");

        // We don't want the bkdr_loader to re-route JTAG mid-transaction, since that will
        // cause us to see an unexpected response, as we will then be talking to an entirely
        // different DMI / DTM (which can also put the RV_DM into a bad state). It will also
        // potentially put the RV_dM debug infrastructure into a bad state. Configure the
        // bkdr_loader to wait long enough so that we can finish our JTAG transaction.
        // FIXME: These calculations are specific to the CW340.
        let jtag_freq_hz: u64 = self.jtag_speed_khz * 1000;
        let soc_clk_wait_cycles =
            CW340_MAIN_CLOCK_FREQ_HZ.div_ceil(jtag_freq_hz) * JTAG_DONE_CYCLES;
        let soc_clk_wait_cycles: u32 = soc_clk_wait_cycles.try_into().unwrap_or_else(|_| {
            log::warn!(
                "Configured JTAG speed ({} kHz) may overflow bkdr_loader wait time.",
                self.jtag_speed_khz
            );
            log::warn!("Configuring maximum wait time.");
            u32::MAX
        });
        self.dmi_write(
            regs::MISSION_MODE_SWITCH_DELAY_REG_OFFSET,
            soc_clk_wait_cycles,
        )
        .context("cannot write FPGA bkdr_loader mission_mode_switch_delay register")?;

        self.dmi_write(regs::CONTROL_REG_OFFSET, 0b1 << regs::CONTROL_DONE_BIT)
            .context("cannot write done to FPGA bkdr_loader control reg")?;

        // Wait until the transition to mission mode is complete and the system exits reset
        // before continuing. For most sensible JTAG speeds this should be basically instant;
        // for very slow speeds (e.g. <= 50 kHz) we need to add some special casing.
        let done_wait_millis = (JTAG_DONE_CYCLES * 1000).div_ceil(jtag_freq_hz);
        std::thread::sleep(Duration::from_millis(done_wait_millis));

        Ok(())
    }

    /// Retrieve information about all of the targets available via the backdoor interface.
    pub fn targets(&self) -> &[BackdoorTargetInfo] {
        &self.targets
    }

    /// Borrow a target by its integer identifier.
    pub fn target_by_id(&self, id: u32) -> Option<BackdoorTarget> {
        let info = self.targets.iter().find(|&t| t.id == id)?;

        Some(BackdoorTarget { info: *info })
    }

    /// Borrow a target by its string identifier.
    pub fn target_by_id_str(&self, id: &str) -> Result<Option<BackdoorTarget>> {
        let encoded_id = BackdoorTargetInfo::id_from_str(id)?;

        Ok(self.target_by_id(encoded_id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifer_str_encoding() {
        let (width, depth) = (1, 1);
        for (id, id_str) in [
            (0x4f545020, "OTP"),
            (0x5352414d, "SRAM"),
            (0x46493031, "FI01"),
        ] {
            assert_eq!(BackdoorTargetInfo { id, width, depth }.id_str(), id_str);
            assert_eq!(BackdoorTargetInfo::id_from_str(id_str).unwrap(), id);
        }
    }
}
