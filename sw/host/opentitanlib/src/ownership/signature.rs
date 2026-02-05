// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use sphincsplus::{SpxDomain, SpxSecretKey};
use std::io::{Read, Write};
use std::path::Path;

use super::GlobalFlags;
use super::misc::{OwnershipKeyAlg, TlvHeader, TlvTag};
use crate::crypto::Error;
use crate::crypto::ecdsa::{EcdsaPrivateKey, EcdsaRawSignature};
use crate::crypto::sha256::Sha256Digest;

#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct DetachedSignature {
    #[serde(
        skip_serializing_if = "GlobalFlags::not_debug",
        default = "DetachedSignature::default_header"
    )]
    pub header: TlvHeader,
    #[serde(default, skip_serializing_if = "GlobalFlags::not_debug")]
    #[annotate(format=hex)]
    pub reserved: [u32; 2],
    #[serde(default)]
    pub command: u32,
    #[serde(default)]
    pub algorithm: OwnershipKeyAlg,
    #[serde(default)]
    pub nonce: u64,
    #[serde(default)]
    pub ecdsa: Option<EcdsaRawSignature>,
    #[serde(default)]
    pub spx: Option<Vec<u8>>,
}

impl Default for DetachedSignature {
    fn default() -> Self {
        Self {
            header: Self::default_header(),
            reserved: [0, 0],
            command: 0,
            algorithm: OwnershipKeyAlg::Unknown,
            nonce: 0,
            ecdsa: None,
            spx: None,
        }
    }
}

impl DetachedSignature {
    const SIZE: usize = 8192;
    const SPX_SIZE: usize = 7856;

    fn default_header() -> TlvHeader {
        TlvHeader::new(TlvTag::DetachedSignature, 0, "0.0")
    }

    pub fn read(src: &mut impl Read, header: TlvHeader) -> Result<Self> {
        let mut reserved = [0u32; 2];
        src.read_u32_into::<LittleEndian>(&mut reserved)?;
        let command = src.read_u32::<LittleEndian>()?;
        let algorithm = OwnershipKeyAlg(src.read_u32::<LittleEndian>()?);
        let nonce = src.read_u64::<LittleEndian>()?;
        let ecdsa = if algorithm.is_ecdsa() {
            Some(EcdsaRawSignature::read(src)?)
        } else {
            None
        };
        let spx = if algorithm.is_spx() {
            let mut spx = vec![0u8; Self::SPX_SIZE];
            src.read_exact(&mut spx)?;
            Some(spx)
        } else {
            None
        };
        Ok(Self {
            header,
            reserved,
            command,
            algorithm,
            nonce,
            ecdsa,
            spx,
        })
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(TlvTag::DetachedSignature, Self::SIZE, "0.0");
        header.write(dest)?;
        for x in &self.reserved {
            dest.write_u32::<LittleEndian>(*x)?;
        }
        dest.write_u32::<LittleEndian>(self.command)?;
        dest.write_u32::<LittleEndian>(u32::from(self.algorithm))?;
        dest.write_u64::<LittleEndian>(self.nonce)?;
        let mut len = 32;
        if self.algorithm.is_ecdsa() {
            let ecdsa = self.ecdsa.as_ref().ok_or_else(|| {
                Error::InvalidSignature(anyhow!(
                    "Algorithm {} requires an ECDSA signature",
                    self.algorithm
                ))
            })?;
            len += ecdsa.write(dest)?;
        }
        if self.algorithm.is_spx() {
            let spx = self.spx.as_ref().ok_or_else(|| {
                Error::InvalidSignature(anyhow!(
                    "Algorithm {} requires an SPX signature",
                    self.algorithm
                ))
            })?;
            dest.write_all(spx.as_slice())?;
            len += spx.len();
        }

        let pad = vec![0xffu8; Self::SIZE - len];
        dest.write_all(&pad)?;
        Ok(())
    }

    pub fn to_vec(&self) -> Result<Vec<u8>> {
        let mut result = Vec::new();
        self.write(&mut result)?;
        Ok(result)
    }

    pub fn new(
        data: &[u8],
        command: u32,
        algorithm: OwnershipKeyAlg,
        nonce: u64,
        ecdsa_key: Option<&EcdsaPrivateKey>,
        spx_key: Option<&SpxSecretKey>,
    ) -> Result<Self> {
        let digest = Sha256Digest::hash(data);
        let ecdsa = if algorithm.is_ecdsa() {
            let key = ecdsa_key.ok_or_else(|| {
                Error::SignFailed(anyhow!("Algorithm {algorithm} requires an ECDSA key"))
            })?;
            Some(key.sign(&digest)?)
        } else {
            None
        };
        let spx = if algorithm.is_spx() {
            let key = spx_key.ok_or_else(|| {
                Error::SignFailed(anyhow!("Algorithm {algorithm} requires an SPX key"))
            })?;
            let (domain, msg) = if algorithm.is_prehashed() {
                let domain = SpxDomain::PreHashedSha256;
                (domain, digest.as_ref())
            } else {
                let domain = SpxDomain::Pure;
                (domain, data)
            };
            Some(key.sign(domain, msg)?)
        } else {
            None
        };

        Ok(Self {
            header: Self::default_header(),
            command,
            algorithm,
            nonce,
            ecdsa,
            spx,
            ..Default::default()
        })
    }

    pub fn from_raw_signatures(
        command: u32,
        algorithm: OwnershipKeyAlg,
        nonce: u64,
        ecdsa_signature_path: Option<&Path>,
        spx_signature_path: Option<&Path>,
    ) -> Result<Self> {
        let mut ecdsa_sig: Option<EcdsaRawSignature> = None;
        let mut spx_sig: Option<Vec<u8>> = None;

        if algorithm.is_ecdsa() {
            let path =
                ecdsa_signature_path.ok_or_else(|| anyhow!("No ecdsa signature provided"))?;
            ecdsa_sig = Some(EcdsaRawSignature::read_from_file(path)?);
        }

        if algorithm.is_spx() {
            let path = spx_signature_path.ok_or_else(|| anyhow!("No spx signature provided"))?;
            let spx_bytes = std::fs::read(path)?;
            spx_sig = Some(spx_bytes);
        }

        Ok(Self {
            header: Self::default_header(),
            command,
            algorithm,
            nonce,
            ecdsa: ecdsa_sig,
            spx: spx_sig,
            ..Default::default()
        })
    }
}
