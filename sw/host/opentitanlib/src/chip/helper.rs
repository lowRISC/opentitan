// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::chip::boot_svc::{OwnershipActivateRequest, OwnershipUnlockRequest, UnlockMode};
use crate::crypto::ecdsa::{EcdsaPrivateKey, EcdsaPublicKey, EcdsaRawPublicKey, EcdsaRawSignature};
use crate::util::parse_int::ParseInt;
use anyhow::Result;
use clap::Args;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

#[derive(Debug, Default, Args)]
pub struct OwnershipUnlockParams {
    #[arg(long, value_enum, help = "Requested unlock mode")]
    pub mode: Option<UnlockMode>,
    #[arg(long, value_parser = u64::from_str, help="Current ROM_EXT nonce")]
    pub nonce: Option<u64>,
    #[arg(long, value_parser = u64::from_str, help="Device Identification Number of the chip")]
    pub din: Option<u64>,
    #[arg(long, help = "A path to the next owner key (for endorsed mode)")]
    pub next_owner: Option<PathBuf>,
    #[arg(long, help = "A path to a detached signature for the unlock request")]
    pub signature: Option<PathBuf>,
    #[arg(long, help = "A path to a private key to sign the request")]
    pub sign: Option<PathBuf>,
}

impl OwnershipUnlockParams {
    /// Applies the parameters to the unlock request.
    pub fn apply(&self, unlock: &mut OwnershipUnlockRequest) -> Result<()> {
        if let Some(mode) = &self.mode {
            unlock.unlock_mode = *mode;
        }
        if let Some(nonce) = &self.nonce {
            unlock.nonce = *nonce;
        }
        if let Some(din) = &self.din {
            unlock.din = *din;
        }
        if let Some(next_owner) = &self.next_owner {
            let key = EcdsaPublicKey::load(next_owner)?;
            unlock.next_owner_key = EcdsaRawPublicKey::try_from(&key)?;
        }
        if let Some(signature) = &self.signature {
            let mut f = File::open(signature)?;
            unlock.signature = EcdsaRawSignature::read(&mut f)?;
        }
        if let Some(sign) = &self.sign {
            let key = EcdsaPrivateKey::load(sign)?;
            unlock.sign(&key)?;
        }
        Ok(())
    }

    /// Reads an unlock request (or creates a default request) and applies the aprameters.
    pub fn apply_to(&self, reader: Option<&mut impl Read>) -> Result<OwnershipUnlockRequest> {
        let mut unlock = if let Some(r) = reader {
            let mut data = Vec::new();
            r.read_to_end(&mut data)?;
            OwnershipUnlockRequest::try_from(data.as_slice())?
        } else {
            OwnershipUnlockRequest::default()
        };
        self.apply(&mut unlock)?;
        Ok(unlock)
    }
}

#[derive(Debug, Default, Args)]
pub struct OwnershipActivateParams {
    #[arg(long, value_parser = u64::from_str, help="Current ROM_EXT nonce")]
    pub nonce: Option<u64>,
    #[arg(long, value_parser = u64::from_str, help="Device Identification Number of the chip")]
    pub din: Option<u64>,
    #[arg(long, help = "A path to a detached signature for the activate request")]
    pub signature: Option<PathBuf>,
    #[arg(long, help = "A path to a private key to sign the request")]
    pub sign: Option<PathBuf>,
}

impl OwnershipActivateParams {
    /// Applies the parameters to the activate request.
    pub fn apply(&self, activate: &mut OwnershipActivateRequest) -> Result<()> {
        if let Some(nonce) = &self.nonce {
            activate.nonce = *nonce;
        }
        if let Some(din) = &self.din {
            activate.din = *din;
        }
        if let Some(signature) = &self.signature {
            let mut f = File::open(signature)?;
            activate.signature = EcdsaRawSignature::read(&mut f)?;
        }
        if let Some(sign) = &self.sign {
            let key = EcdsaPrivateKey::load(sign)?;
            activate.sign(&key)?;
        }
        Ok(())
    }

    /// Reads an activate request (or creates a default request) and applies the parameters.
    pub fn apply_to(&self, reader: Option<&mut impl Read>) -> Result<OwnershipActivateRequest> {
        let mut activate = if let Some(r) = reader {
            let mut data = Vec::new();
            r.read_to_end(&mut data)?;
            OwnershipActivateRequest::try_from(data.as_slice())?
        } else {
            OwnershipActivateRequest::default()
        };
        self.apply(&mut activate)?;
        Ok(activate)
    }
}
