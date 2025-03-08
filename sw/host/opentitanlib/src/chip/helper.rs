// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use sphincsplus::{DecodeKey, SpxSecretKey};
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use crate::chip::boot_svc::{OwnershipActivateRequest, OwnershipUnlockRequest, UnlockMode};
use crate::crypto::ecdsa::{EcdsaPrivateKey, EcdsaPublicKey, EcdsaRawPublicKey, EcdsaRawSignature};
use crate::ownership::{DetachedSignature, OwnershipKeyAlg};
use crate::util::parse_int::ParseInt;

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
    #[arg(
        long,
        help = "A path to an external ECDSA signature for the unlock request"
    )]
    pub signature: Option<PathBuf>,
    #[arg(long, default_value_t = OwnershipKeyAlg::EcdsaP256, help = "The algorithm used to sign the request")]
    pub algorithm: OwnershipKeyAlg,
    #[arg(long, help = "A path to a private ECDSA key to sign the request")]
    pub ecdsa_key: Option<PathBuf>,
    #[arg(long, help = "A path to a private SPX key to sign the request")]
    pub spx_key: Option<PathBuf>,
}

impl OwnershipUnlockParams {
    /// Applies the parameters to the unlock request.
    pub fn apply(&self, unlock: &mut OwnershipUnlockRequest) -> Result<Option<DetachedSignature>> {
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
            // TODO: Recognize both a raw ECDSA signature and/or a detached signature struct
            // containing only an ECDSA signature.
            let mut f = File::open(signature)?;
            unlock.signature = EcdsaRawSignature::read(&mut f)?;
        }
        if self.ecdsa_key.is_some() || self.spx_key.is_some() {
            let ecdsa_key = self
                .ecdsa_key
                .as_ref()
                .map(EcdsaPrivateKey::load)
                .transpose()?;
            let spx_key = self
                .spx_key
                .as_ref()
                .map(SpxSecretKey::read_pem_file)
                .transpose()?;
            let signature =
                unlock.detached_sign(self.algorithm, ecdsa_key.as_ref(), spx_key.as_ref())?;
            if !self.algorithm.is_detached() {
                unlock.signature = signature.ecdsa.clone().expect("ECDSA signature");
            }
            Ok(Some(signature))
        } else {
            Ok(None)
        }
    }

    /// Reads an unlock request (or creates a default request) and applies the aprameters.
    pub fn apply_to(
        &self,
        reader: Option<&mut impl Read>,
    ) -> Result<(OwnershipUnlockRequest, Option<DetachedSignature>)> {
        let mut unlock = if let Some(r) = reader {
            let mut data = Vec::new();
            r.read_to_end(&mut data)?;
            OwnershipUnlockRequest::try_from(data.as_slice())?
        } else {
            OwnershipUnlockRequest::default()
        };
        let signature = self.apply(&mut unlock)?;
        Ok((unlock, signature))
    }
}

#[derive(Debug, Default, Args)]
pub struct OwnershipActivateParams {
    #[arg(long, value_parser = u64::from_str, help="Current ROM_EXT nonce")]
    pub nonce: Option<u64>,
    #[arg(long, value_parser = u64::from_str, help="Device Identification Number of the chip")]
    pub din: Option<u64>,
    #[arg(
        long,
        help = "A path to an external ECDSA signature for the activate request"
    )]
    pub signature: Option<PathBuf>,
    #[arg(long, default_value_t = OwnershipKeyAlg::EcdsaP256, help = "The algorithm used to sign the request")]
    pub algorithm: OwnershipKeyAlg,
    #[arg(long, help = "A path to a private ECDSA key to sign the request")]
    pub ecdsa_key: Option<PathBuf>,
    #[arg(long, help = "A path to a private SPX key to sign the request")]
    pub spx_key: Option<PathBuf>,
}

impl OwnershipActivateParams {
    /// Applies the parameters to the activate request.
    pub fn apply(
        &self,
        activate: &mut OwnershipActivateRequest,
    ) -> Result<Option<DetachedSignature>> {
        if let Some(nonce) = &self.nonce {
            activate.nonce = *nonce;
        }
        if let Some(din) = &self.din {
            activate.din = *din;
        }
        if let Some(signature) = &self.signature {
            // TODO: Recognize both a raw ECDSA signature and/or a detached signature struct
            // containing only an ECDSA signature.
            let mut f = File::open(signature)?;
            activate.signature = EcdsaRawSignature::read(&mut f)?;
        }
        if self.ecdsa_key.is_some() || self.spx_key.is_some() {
            let ecdsa_key = self
                .ecdsa_key
                .as_ref()
                .map(EcdsaPrivateKey::load)
                .transpose()?;
            let spx_key = self
                .spx_key
                .as_ref()
                .map(SpxSecretKey::read_pem_file)
                .transpose()?;
            let signature =
                activate.detached_sign(self.algorithm, ecdsa_key.as_ref(), spx_key.as_ref())?;
            if !self.algorithm.is_detached() {
                activate.signature = signature.ecdsa.clone().expect("ECDSA signature");
            }
            Ok(Some(signature))
        } else {
            Ok(None)
        }
    }

    /// Reads an activate request (or creates a default request) and applies the parameters.
    pub fn apply_to(
        &self,
        reader: Option<&mut impl Read>,
    ) -> Result<(OwnershipActivateRequest, Option<DetachedSignature>)> {
        let mut activate = if let Some(r) = reader {
            let mut data = Vec::new();
            r.read_to_end(&mut data)?;
            OwnershipActivateRequest::try_from(data.as_slice())?
        } else {
            OwnershipActivateRequest::default()
        };
        let signature = self.apply(&mut activate)?;
        Ok((activate, signature))
    }
}
