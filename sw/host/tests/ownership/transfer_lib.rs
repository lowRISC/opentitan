// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{anyhow, Result};
use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_log::BootLog;
use opentitanlib::chip::boot_svc::{Message, UnlockMode};
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
use opentitanlib::crypto::ecdsa::EcdsaPrivateKey;
use opentitanlib::crypto::rsa::RsaPublicKey;
use opentitanlib::ownership::{
    ApplicationKeyDomain, KeyMaterial, OwnerApplicationKey, OwnerBlock, OwnerConfigItem,
    OwnershipKeyAlg,
};
use opentitanlib::rescue::serial::RescueSerial;

use std::path::Path;

/// Gets the BootLog.
pub fn get_boot_log(transport: &TransportWrapper, rescue: &RescueSerial) -> Result<BootLog> {
    rescue.enter(transport, /*reset=*/ true)?;
    rescue.get_boot_log()
}

/// Prepares an UnlockOwnership command, sends it to the chip and gets the response.
pub fn ownership_unlock(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    mode: UnlockMode,
    nonce: u64,
    unlock_key: &Path,
    next_owner: Option<&Path>,
) -> Result<()> {
    let unlock = OwnershipUnlockParams {
        mode: Some(mode),
        nonce: Some(nonce),
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
    unlock_key: &Path,
) -> Result<()> {
    ownership_unlock(transport, rescue, UnlockMode::Any, nonce, unlock_key, None)
}

/// Prepares an OwnershipActivate command, sends it to the chip and gets the response.
pub fn ownership_activate(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    nonce: u64,
    activate_key: &Path,
) -> Result<()> {
    let activate = OwnershipActivateParams {
        nonce: Some(nonce),
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

/// Prepares an OwnerBlock and sends it to the chip.
pub fn create_owner(
    transport: &TransportWrapper,
    rescue: &RescueSerial,
    owner_key: &Path,
    activate_key: &Path,
    unlock_key: &Path,
    app_key: &Path,
    corrupt_signature: bool,
) -> Result<()> {
    let owner_key = EcdsaPrivateKey::load(owner_key)?;
    let activate_key = EcdsaPrivateKey::load(activate_key)?;
    let unlock_key = EcdsaPrivateKey::load(unlock_key)?;
    let app_key = RsaPublicKey::from_pkcs1_der_file(app_key)?;
    let mut owner = OwnerBlock {
        owner_key: KeyMaterial::Ecdsa(owner_key.public_key().try_into()?),
        activate_key: KeyMaterial::Ecdsa(activate_key.public_key().try_into()?),
        unlock_key: KeyMaterial::Ecdsa(unlock_key.public_key().try_into()?),
        data: vec![OwnerConfigItem::ApplicationKey(OwnerApplicationKey {
            key_alg: OwnershipKeyAlg::Rsa,
            key_domain: ApplicationKeyDomain::Prod,
            key: KeyMaterial::Rsa(app_key.try_into()?),
            ..Default::default()
        })],
        ..Default::default()
    };
    owner.sign(&owner_key)?;
    if corrupt_signature {
        owner.signature.r[0] += 1;
    }
    let mut owner_config = Vec::new();
    owner.write(&mut owner_config)?;
    rescue.enter(transport, /*reset=*/ true)?;
    rescue.set_owner_config(&owner_config)?;
    Ok(())
}
