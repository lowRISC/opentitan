// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Context, Result, anyhow};
use clap::{Args, Parser, Subcommand, ValueEnum};

use std::io::Cursor;
use std::path::Path;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_log::OwnershipState;
use opentitanlib::chip::boot_svc::BootSlot;
use opentitanlib::chip::device_id::DeviceId;
use opentitanlib::image::image::{self};
use opentitanlib::rescue::{EntryMode, RescueParams};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::util::file::FromReader;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(subcommand)]
    command: Commands,

    // Device ID represented as a hexadecimal string.
    // This format should correspond to how the ID is structured or stored
    // in the device's OTP.
    #[arg(long)]
    device_id: Option<String>,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

#[derive(Clone, Debug, Args)]
struct RescueCommand {
    #[command(flatten)]
    params: RescueParams,

    #[arg(long)]
    action: RescueTestActions,
}

#[derive(Debug, Subcommand)]
enum Commands {
    Rescue(RescueCommand),
}

#[derive(ValueEnum, Debug, Clone, Copy, PartialEq)]
pub enum RescueTestActions {
    GetDeviceId,
    GetBootLog,
}

fn get_device_id_test(
    expected_device_id_hex: &String,
    params: &RescueParams,
    transport: &TransportWrapper,
) -> Result<()> {
    let rescue = params.create(transport)?;
    rescue.enter(transport, EntryMode::Reset)?;
    let actual_device_id_from_rescue = rescue.get_device_id()?;
    let mut bytes_from_hex = hex::decode(expected_device_id_hex).map_err(|e| {
        anyhow!(
            "Failed to decode hex string '{}': {}",
            expected_device_id_hex,
            e
        )
    })?;
    // This reversal is to swap the byte order of the entire decoded hex sequence
    // to match the endianness expectation of the DeviceId::read function.
    bytes_from_hex.reverse();
    let mut cursor = Cursor::new(bytes_from_hex);
    let parsed_expected_device_id = DeviceId::read(&mut cursor).unwrap();
    if parsed_expected_device_id == actual_device_id_from_rescue {
        Ok(())
    } else {
        Err(anyhow!(
            "Device ID mismatch. Expected: {:?}, but got: {:?}",
            parsed_expected_device_id,
            actual_device_id_from_rescue
        ))
    }
}

fn get_boot_log_test(
    binary: &Path,
    params: &RescueParams,
    transport: &TransportWrapper,
) -> Result<()> {
    const BOOT_LOG_IDENTIFIER: u32 = u32::from_le_bytes(*b"BLOG");
    let image = image::Image::read_from_file(binary)?;
    let rescue = params.create(transport)?;
    rescue.enter(transport, EntryMode::Reset)?;
    let boot_log = rescue
        .get_boot_log()
        .context("Failed to get boot log from rescue")?;
    let rom_ext_manifest = image
        .subimages()?
        .first()
        .ok_or_else(|| anyhow!("No subimages found in the image"))?
        .manifest;
    if boot_log.rom_ext_major != rom_ext_manifest.version_major {
        return Err(anyhow!(
            "rom_ext_major mismatch. Expected: {}, but got: {}",
            rom_ext_manifest.version_major,
            boot_log.rom_ext_major
        ));
    }

    if boot_log.rom_ext_minor != rom_ext_manifest.version_minor {
        return Err(anyhow!(
            "rom_ext_minor mismatch. Expected: {}, but got: {}",
            rom_ext_manifest.version_minor,
            boot_log.rom_ext_minor
        ));
    }

    if boot_log.ownership_state != OwnershipState::LockedOwner {
        return Err(anyhow!(
            "ownership_state mismatch. Expected: {}, but got: {}",
            OwnershipState::LockedOwner,
            boot_log.ownership_state
        ));
    }

    if boot_log.identifier != BOOT_LOG_IDENTIFIER {
        return Err(anyhow!(
            "identifier mismatch. Expected: {}, but got: {}",
            BOOT_LOG_IDENTIFIER,
            boot_log.identifier
        ));
    }

    if boot_log.rom_ext_slot != BootSlot::SlotA {
        return Err(anyhow!(
            "rom_ext_slot mismatch. Expected: {}, but got: {}",
            BootSlot::SlotA,
            boot_log.rom_ext_slot
        ));
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    match opts.command {
        Commands::Rescue(rescue) => match rescue.action {
            RescueTestActions::GetDeviceId => {
                let device_id = &opts
                    .device_id
                    .as_ref()
                    .ok_or_else(|| anyhow!("No device_id provided"))?;
                get_device_id_test(device_id, &rescue.params, &transport)?;
            }
            RescueTestActions::GetBootLog => {
                let binary = &opts
                    .init
                    .bootstrap
                    .bootstrap
                    .as_ref()
                    .ok_or_else(|| anyhow!("No RV32 test binary provided"))?;
                get_boot_log_test(binary, &rescue.params, &transport)?;
            }
        },
    }
    Ok(())
}
