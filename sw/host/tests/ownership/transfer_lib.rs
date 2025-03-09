// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Result, anyhow};
use clap::ValueEnum;
use sphincsplus::{DecodeKey, SpxPublicKey, SpxSecretKey};
use std::path::{Path, PathBuf};

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_log::BootLog;
use opentitanlib::chip::boot_svc::BootSlot;
use opentitanlib::chip::boot_svc::{Message, UnlockMode};
use opentitanlib::chip::device_id::DeviceId;
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
use opentitanlib::crypto::ecdsa::{EcdsaPrivateKey, EcdsaPublicKey};
use opentitanlib::ownership::{
    ApplicationKeyDomain, CommandTag, FlashFlags, HybridRawPublicKey, KeyMaterial,
    OwnerApplicationKey, OwnerBlock, OwnerConfigItem, OwnerFlashConfig, OwnerFlashInfoConfig,
    OwnerFlashRegion, OwnerInfoPage, OwnerRescueConfig, OwnershipKeyAlg,
};
use opentitanlib::rescue::Rescue;
use opentitanlib::rescue::serial::RescueSerial;

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
#[allow(clippy::too_many_arguments)]
pub fn ownership_unlock(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    mode: UnlockMode,
    nonce: u64,
    din: u64,
    algorithm: OwnershipKeyAlg,
    ecdsa_key: Option<PathBuf>,
    spx_key: Option<PathBuf>,
    next_owner: Option<&Path>,
) -> Result<()> {
    let (unlock, detached_sig) = OwnershipUnlockParams {
        mode: Some(mode),
        nonce: Some(nonce),
        din: Some(din),
        next_owner: next_owner.map(|p| p.into()),
        algorithm,
        ecdsa_key,
        spx_key,
        ..Default::default()
    }
    .apply_to(Option::<&mut std::fs::File>::None)?;

    rescue.enter(transport, /*reset=*/ true)?;
    rescue.wait()?;
    if algorithm.is_detached() {
        let sig = detached_sig.expect("algorithm is detached");
        rescue.update_firmware(BootSlot::SlotA, sig.to_vec()?.as_slice())?;
    }
    rescue.ownership_unlock(unlock)?;
    rescue.reboot()?;
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
    algorithm: OwnershipKeyAlg,
    ecdsa_key: Option<PathBuf>,
    spx_key: Option<PathBuf>,
) -> Result<()> {
    ownership_unlock(
        transport,
        rescue,
        UnlockMode::Any,
        nonce,
        din,
        algorithm,
        ecdsa_key,
        spx_key,
        None,
    )
}

/// Prepares an OwnershipActivate command, sends it to the chip and gets the response.
pub fn ownership_activate(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    nonce: u64,
    din: u64,
    algorithm: OwnershipKeyAlg,
    ecdsa_key: Option<PathBuf>,
    spx_key: Option<PathBuf>,
) -> Result<()> {
    let (activate, detached_sig) = OwnershipActivateParams {
        nonce: Some(nonce),
        din: Some(din),
        algorithm,
        ecdsa_key,
        spx_key,
        ..Default::default()
    }
    .apply_to(Option::<&mut std::fs::File>::None)?;

    rescue.enter(transport, /*reset=*/ true)?;
    rescue.wait()?;
    if algorithm.is_detached() {
        let sig = detached_sig.expect("algorithm is detached");
        rescue.update_firmware(BootSlot::SlotA, sig.to_vec()?.as_slice())?;
    }
    rescue.ownership_activate(activate)?;
    rescue.reboot()?;
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

pub struct HybridPair {
    pub ecdsa: Option<EcdsaPrivateKey>,
    pub spx: Option<SpxSecretKey>,
}

impl HybridPair {
    pub fn load(ecdsa: Option<&Path>, spx: Option<&Path>) -> Result<Self> {
        Ok(Self {
            ecdsa: ecdsa.map(EcdsaPrivateKey::load).transpose()?,
            spx: spx.map(SpxSecretKey::read_pem_file).transpose()?,
        })
    }

    pub fn check(&self, key_alg: OwnershipKeyAlg, name: &str) -> Result<()> {
        if key_alg.is_ecdsa() && self.ecdsa.is_none() {
            return Err(anyhow!("{name} using {key_alg} requires an ECDSA key"));
        }
        if !key_alg.is_ecdsa() && self.ecdsa.is_some() {
            return Err(anyhow!(
                "{name} using {key_alg} has an ECDSA key, but doesn't need one"
            ));
        }
        if key_alg.is_spx() && self.spx.is_none() {
            return Err(anyhow!("{name} using {key_alg} requires an SPX key"));
        }
        if !key_alg.is_spx() && self.spx.is_some() {
            return Err(anyhow!(
                "{name} using {key_alg} has an SPX key, but doesn't need one"
            ));
        }
        Ok(())
    }

    pub fn key_material(&self) -> Result<KeyMaterial> {
        match (&self.ecdsa, &self.spx) {
            (Some(ecdsa), None) => Ok(KeyMaterial::Ecdsa(ecdsa.public_key().try_into()?)),
            (None, Some(spx)) => Ok(KeyMaterial::Spx(SpxPublicKey::from(spx).try_into()?)),
            (Some(ecdsa), Some(spx)) => Ok(KeyMaterial::Hybrid(HybridRawPublicKey {
                ecdsa: ecdsa.public_key().try_into()?,
                spx: SpxPublicKey::from(spx).try_into()?,
            })),
            _ => Err(anyhow!("No keys to load")),
        }
    }
}

/// Prepares an OwnerBlock and sends it to the chip.
#[allow(clippy::too_many_arguments)]
pub fn create_owner<F>(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    nonce: u64,
    key_alg: OwnershipKeyAlg,
    owner_key: HybridPair,
    activate_key: HybridPair,
    unlock_key: HybridPair,
    app_key: &Path,
    config: OwnerConfigKind,
    customize: F,
) -> Result<()>
where
    F: Fn(&mut OwnerBlock),
{
    owner_key.check(key_alg, "owner key")?;
    activate_key.check(key_alg, "activate key")?;
    unlock_key.check(key_alg, "unlock key")?;
    let cfg = config as u32;
    let app_key = EcdsaPublicKey::load(app_key)?;
    let constraint = if cfg & CFG_APP_CONSTRAINT == 0 {
        0
    } else {
        // Constrain to the DIN field of device_id.
        0x6
    };
    let mut owner = OwnerBlock {
        ownership_key_alg: key_alg,
        owner_key: owner_key.key_material()?,
        activate_key: activate_key.key_material()?,
        unlock_key: unlock_key.key_material()?,
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
        let flash_config = if cfg & CFG_FLASH_ERROR != 0 {
            // It is an error set have a flash config that overlaps the ROM_EXT
            // region.

            // Side A: 0-64K romext, 64-448K firmware, 448-512K filesystem.
            vec![
                OwnerFlashRegion::new(0, 32, config.rom_ext()),
                OwnerFlashRegion::new(32, 192, config.firmware()),
                OwnerFlashRegion::new(224, 32, config.filesystem()),
                // Side B: 0-64K romext, 64-448K firmware, 448-512K filesystem.
                OwnerFlashRegion::new(256, 32, config.rom_ext()),
                OwnerFlashRegion::new(256 + 32, 192, config.firmware()),
                OwnerFlashRegion::new(256 + 224, 32, config.filesystem()),
            ]
        } else {
            vec![
                // Side A: 64-448K firmware, 448-512K filesystem.
                OwnerFlashRegion::new(32, 192, config.firmware()),
                OwnerFlashRegion::new(224, 32, config.filesystem()),
                // Side B: 64-448K firmware, 448-512K filesystem.
                OwnerFlashRegion::new(256 + 32, 192, config.firmware()),
                OwnerFlashRegion::new(256 + 224, 32, config.filesystem()),
            ]
        };
        owner
            .data
            .push(OwnerConfigItem::FlashConfig(OwnerFlashConfig {
                config: flash_config,
                ..Default::default()
            }));
        owner
            .data
            .push(OwnerConfigItem::FlashInfoConfig(OwnerFlashInfoConfig {
                config: vec![
                    // Bank 1, page 5, filesystem-like configuration.
                    OwnerInfoPage::new(1, 5, config.filesystem()),
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
    let mut detached_sig =
        owner.detached_sign(nonce, owner_key.ecdsa.as_ref(), owner_key.spx.as_ref())?;
    if cfg & CFG_CORRUPT != 0 {
        if let Some(val) = detached_sig.ecdsa.as_mut() {
            val.r[0] ^= 1;
        }
        if let Some(val) = detached_sig.spx.as_mut() {
            val[0] ^= 1;
        }
    }
    if !key_alg.is_detached() {
        owner.signature = detached_sig.ecdsa.clone().expect("ecdsa signature");
    }
    let mut owner_config = Vec::new();
    owner.write(&mut owner_config)?;
    rescue.enter(transport, /*reset=*/ true)?;
    rescue.wait()?;
    if key_alg.is_detached() {
        rescue.update_firmware(BootSlot::SlotB, detached_sig.to_vec()?.as_slice())?;
    }
    rescue.set_owner_config(&owner_config)?;
    rescue.reboot()?;
    Ok(())
}
