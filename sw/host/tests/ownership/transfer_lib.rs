// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{anyhow, Result};
use clap::ValueEnum;
use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_log::BootLog;
use opentitanlib::chip::boot_svc::{Message, UnlockMode};
use opentitanlib::chip::device_id::DeviceId;
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
use opentitanlib::crypto::ecdsa::{EcdsaPrivateKey, EcdsaPublicKey};
use opentitanlib::ownership::{
    ApplicationKeyDomain, CommandTag, FlashFlags, KeyMaterial, OwnerApplicationKey, OwnerBlock,
    OwnerConfigItem, OwnerFlashConfig, OwnerFlashRegion, OwnerRescueConfig, OwnershipKeyAlg,
};
use opentitanlib::rescue::serial::RescueSerial;

use std::path::Path;

pub const TEST_OWNER_CONFIG_VERSION: u32 = 1;

/// Gets the BootLog.
pub fn get_device_info(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
) -> Result<(BootLog, DeviceId)> {
    rescue.enter(transport, /*reset=*/ true)?;
    Ok((rescue.get_boot_log()?, rescue.get_device_id()?))
}

/// Prepares an UnlockOwnership command, sends it to the chip and gets the response.
pub fn ownership_unlock(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    mode: UnlockMode,
    nonce: u64,
    din: u64,
    unlock_key: &Path,
    next_owner: Option<&Path>,
) -> Result<()> {
    let unlock = OwnershipUnlockParams {
        mode: Some(mode),
        nonce: Some(nonce),
        din: Some(din),
        next_owner: next_owner.map(|p| p.into()),
        sign: Some(unlock_key.into()),
        ..Default::default()
    }
    .apply_to(Option::<&mut std::fs::File>::None)?;

    rescue.enter(transport, /*reset=*/ true)?;
    rescue.ownership_unlock(unlock)?;
    rescue.enter(transport, /*reset=*/ false)?;
    let result = rescue.get_boot_svc()?;
    match result.message {
        Message::OwnershipUnlockResponse(r) => r.status.into(),
        _ => Err(anyhow!("Unexpected response: {result:x?}")),
    }
}

/// Prepares an UnlockOwnership command (with UnlockMode::Any), sends it to the chip and gets the response.
pub fn ownership_unlock_any(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    nonce: u64,
    din: u64,
    unlock_key: &Path,
) -> Result<()> {
    ownership_unlock(
        transport,
        rescue,
        UnlockMode::Any,
        nonce,
        din,
        unlock_key,
        None,
    )
}

/// Prepares an OwnershipActivate command, sends it to the chip and gets the response.
pub fn ownership_activate(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    nonce: u64,
    din: u64,
    activate_key: &Path,
) -> Result<()> {
    let activate = OwnershipActivateParams {
        nonce: Some(nonce),
        din: Some(din),
        sign: Some(activate_key.into()),
        ..Default::default()
    }
    .apply_to(Option::<&mut std::fs::File>::None)?;

    rescue.enter(transport, /*reset=*/ true)?;
    rescue.ownership_activate(activate)?;
    rescue.enter(transport, /*reset=*/ false)?;
    let result = rescue.get_boot_svc()?;
    match &result.message {
        Message::OwnershipActivateResponse(r) => r.status.into(),
        _ => Err(anyhow!("Unexpected response: {result:x?}")),
    }
}

// These flags request certain features of the ownership configuration.
// The names like "FLASH1" or "RESCUE1" don't have any special significance
// other than to give them a distinct name.

// Request to corrupt the owner config block.
const CFG_CORRUPT: u32 = 0x0000_0001;
// Request a config with a flash configuration.
const CFG_FLASH1: u32 = 0x0000_0002;
// Request flash config lockdown in the flash configuration.
const CFG_FLASH_LOCK: u32 = 0x0000_0004;
// Request a config with a rescue configuration.
const CFG_RESCUE1: u32 = 0x0000_0008;
// Request a rescue configuration that restricts the set of allowed commands
// (e.g. this one removes "SetNextBl0Slot" from the set of allowed commands).
const CFG_RESCUE_RESTRICT: u32 = 0x0000_0010;
// Request a configuration where the application key has a usage constraint.
const CFG_APP_CONSTRAINT: u32 = 0x0000_0020;
// Request a bad ROM_EXT flash config region.
const CFG_FLASH_ERROR: u32 = 0x0000_0040;

#[repr(u32)]
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum OwnerConfigKind {
    #[default]
    Basic = 0,
    Corrupt = CFG_CORRUPT,
    WithFlash = CFG_FLASH1 | CFG_RESCUE1,
    WithFlashLocked = CFG_FLASH1 | CFG_RESCUE1 | CFG_FLASH_LOCK,
    WithFlashError = CFG_FLASH1 | CFG_RESCUE1 | CFG_FLASH_LOCK | CFG_FLASH_ERROR,
    WithRescue = CFG_RESCUE1,
    WithRescueRestricted = CFG_FLASH1 | CFG_RESCUE1 | CFG_RESCUE_RESTRICT,
    WithAppConstraint = CFG_APP_CONSTRAINT,
}

impl OwnerConfigKind {
    pub fn is_flash_locked(self) -> bool {
        self as u32 & CFG_FLASH_LOCK != 0
    }

    fn rom_ext(self) -> FlashFlags {
        FlashFlags {
            read: true,
            program: true,
            erase: true,
            // Maybe turn on scrambling & ECC for the ROM_EXT region.
            scramble: self as u32 & CFG_FLASH_ERROR != 0,
            ecc: self as u32 & CFG_FLASH_ERROR != 0,
            high_endurance: false,
            protect_when_active: true,
            lock: self.is_flash_locked(),
        }
    }

    fn firmware(self) -> FlashFlags {
        FlashFlags {
            read: true,
            program: true,
            erase: true,
            scramble: true,
            ecc: true,
            high_endurance: false,
            protect_when_active: true,
            lock: self.is_flash_locked(),
        }
    }

    fn filesystem(self) -> FlashFlags {
        FlashFlags {
            read: true,
            program: true,
            erase: true,
            scramble: false,
            ecc: false,
            high_endurance: true,
            protect_when_active: false,
            lock: self.is_flash_locked(),
        }
    }
}

/// Prepares an OwnerBlock and sends it to the chip.
#[allow(clippy::too_many_arguments)]
pub fn create_owner<F>(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    owner_key: &Path,
    activate_key: &Path,
    unlock_key: &Path,
    app_key: &Path,
    config: OwnerConfigKind,
    customize: F,
) -> Result<()>
where
    F: Fn(&mut OwnerBlock),
{
    let cfg = config as u32;
    let owner_key = EcdsaPrivateKey::load(owner_key)?;
    let activate_key = EcdsaPrivateKey::load(activate_key)?;
    let unlock_key = EcdsaPrivateKey::load(unlock_key)?;
    let app_key = EcdsaPublicKey::load(app_key)?;
    let constraint = if cfg & CFG_APP_CONSTRAINT == 0 {
        0
    } else {
        // Constrain to the DIN field of device_id.
        0x6
    };
    let mut owner = OwnerBlock {
        ownership_key_alg: OwnershipKeyAlg::EcdsaP256,
        owner_key: KeyMaterial::Ecdsa(owner_key.public_key().try_into()?),
        activate_key: KeyMaterial::Ecdsa(activate_key.public_key().try_into()?),
        unlock_key: KeyMaterial::Ecdsa(unlock_key.public_key().try_into()?),
        data: vec![OwnerConfigItem::ApplicationKey(OwnerApplicationKey {
            key_alg: OwnershipKeyAlg::EcdsaP256,
            usage_constraint: constraint,
            key_domain: ApplicationKeyDomain::Prod,
            key: KeyMaterial::Ecdsa(app_key.try_into()?),
            ..Default::default()
        })],
        ..Default::default()
    };
    if cfg & CFG_FLASH1 != 0 {
        owner
            .data
            .push(OwnerConfigItem::FlashConfig(OwnerFlashConfig {
                config: vec![
                    // Side A: 0-64K romext, 64-448K firmware, 448-512K filesystem.
                    OwnerFlashRegion::new(0, 32, config.rom_ext()),
                    OwnerFlashRegion::new(32, 192, config.firmware()),
                    OwnerFlashRegion::new(224, 32, config.filesystem()),
                    // Side B: 0-64K romext, 64-448K firmware, 448-512K filesystem.
                    OwnerFlashRegion::new(256, 32, config.rom_ext()),
                    OwnerFlashRegion::new(256 + 32, 192, config.firmware()),
                    OwnerFlashRegion::new(256 + 224, 32, config.filesystem()),
                ],
                ..Default::default()
            }));
    }
    if cfg & CFG_RESCUE1 != 0 {
        let mut rescue = OwnerRescueConfig::all();
        rescue.start = 32;
        rescue.size = 192;
        if cfg & CFG_RESCUE_RESTRICT != 0 {
            // Restrict one of the boot_svc commands in "restrict" mode.
            rescue
                .command_allow
                .retain(|t| *t != CommandTag::NextBl0SlotRequest);
        }
        owner.data.push(OwnerConfigItem::RescueConfig(rescue));
    }
    customize(&mut owner);
    owner.sign(&owner_key)?;
    if cfg & CFG_CORRUPT != 0 {
        owner.signature.r[0] += 1;
    }
    let mut owner_config = Vec::new();
    owner.write(&mut owner_config)?;
    rescue.enter(transport, /*reset=*/ true)?;
    rescue.set_owner_config(&owner_config)?;
    Ok(())
}
