// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow, ensure};
use clap::{Args, Subcommand, ValueEnum};
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::PathBuf;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
use opentitanlib::crypto::ecdsa::{EcdsaPrivateKey, EcdsaPublicKey, EcdsaRawSignature};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::ownership::{
    DetachedSignature, DetachedSignatureCommand, GlobalFlags, KeyMaterial, OwnerBlock,
    OwnershipKeyAlg, TlvHeader,
};
use sphincsplus::{DecodeKey, SphincsPlus, SpxDomain, SpxPublicKey, SpxRawSignature};

#[derive(ValueEnum, Debug, Clone, Copy, PartialEq)]
enum Format {
    Auto,
    Text,
    Binary,
}

#[derive(Debug, Args)]
pub struct OwnershipConfigCommand {
    #[arg(long, help = "Show header and reserved fields")]
    debug: bool,
    #[arg(long, help = "Use the basic ownership block", conflicts_with = "input")]
    basic: bool,
    #[arg(
        short,
        long,
        help = "A file containing an ownership config block",
        conflicts_with = "basic",
        required_unless_present("basic")
    )]
    input: Option<PathBuf>,
    #[arg(long, value_enum, default_value_t = Format::Auto, help = "Input format")]
    inform: Format,
    #[arg(long, help = "A path to a detached signature for the owner block")]
    pub signature: Option<PathBuf>,
    #[arg(long, help = "A path to a private key to sign the request")]
    pub sign: Option<PathBuf>,
    #[arg(help = "Binary output file path")]
    output: Option<PathBuf>,
}

impl CommandDispatch for OwnershipConfigCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        GlobalFlags::set_debug(self.debug);
        let mut config = if self.basic {
            OwnerBlock::basic()
        } else {
            let input = std::fs::read(self.input.as_ref().unwrap())?;
            let mut inform = self.inform;
            if inform == Format::Auto {
                inform = match input[0] {
                    b'{' | b'#' | b'/' | b'\n' => Format::Text,
                    _ => Format::Binary,
                };
            }
            match inform {
                Format::Text => {
                    let text = std::str::from_utf8(&input)?;
                    serde_annotate::from_str::<OwnerBlock>(text)?
                }
                Format::Binary => {
                    let mut cursor = std::io::Cursor::new(&input);
                    let header = TlvHeader::read(&mut cursor)?;
                    OwnerBlock::read(&mut cursor, header)?
                }
                _ => unreachable!(),
            }
        };

        if let Some(signature) = &self.signature {
            let mut f = File::open(signature)?;
            config.signature = EcdsaRawSignature::read(&mut f)?;
        }
        if let Some(sign) = &self.sign {
            let key = EcdsaPrivateKey::load(sign)?;
            config.sign(&key)?;
        }

        if let Some(output) = &self.output {
            let mut f = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(output)?;
            config.write(&mut f)?;
            Ok(None)
        } else {
            Ok(Some(Box::new(config)))
        }
    }
}

#[derive(Debug, Args)]
pub struct OwnershipUnlockCommand {
    #[command(flatten)]
    params: OwnershipUnlockParams,
    #[arg(short, long, help = "Filename to write the detached signature")]
    detached: Option<PathBuf>,
    #[arg(short, long, help = "A file containing a binary unlock request")]
    input: Option<PathBuf>,
    #[arg(
        value_name = "FILE",
        help = "A file to write out a binary unlock request"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for OwnershipUnlockCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let (unlock, signature) = self
            .params
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;
        if let Some(output) = &self.output {
            let mut f = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(output)?;

            unlock.write(&mut f)?;
        }
        if self.params.algorithm.is_detached() && signature.is_some() && self.detached.is_none() {
            log::warn!(
                "The algorithm {} requires a detached signature, but no detach signature file was specified.",
                self.params.algorithm
            );
        }
        if let Some(detached) = &self.detached {
            ensure!(
                signature.is_some(),
                anyhow!(
                    "Requested to save the detached signature, but there is no detached signature."
                )
            );
            let mut f = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(detached)?;
            signature.unwrap().write(&mut f)?;
        }

        Ok(Some(Box::new(unlock)))
    }
}

#[derive(Debug, Args)]
pub struct OwnershipActivateCommand {
    #[command(flatten)]
    params: OwnershipActivateParams,
    #[arg(short, long, help = "Filename to write the detached signature")]
    detached: Option<PathBuf>,
    #[arg(short, long, help = "A file containing a binary unlock request")]
    input: Option<PathBuf>,
    #[arg(
        value_name = "FILE",
        help = "A file to write out a binary unlock request"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for OwnershipActivateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let (activate, signature) = self
            .params
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;
        if let Some(output) = &self.output {
            let mut f = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(output)?;
            activate.write(&mut f)?;
        }
        if self.params.algorithm.is_detached() && signature.is_some() && self.detached.is_none() {
            log::warn!(
                "The algorithm {} requires a detached signature, but no detach signature file was specified.",
                self.params.algorithm
            );
        }
        if let Some(detached) = &self.detached {
            ensure!(
                signature.is_some(),
                anyhow!(
                    "Requested to save the detached signature, but there is no detached signature."
                )
            );
            let mut f = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(detached)?;
            signature.unwrap().write(&mut f)?;
        }
        Ok(Some(Box::new(activate)))
    }
}

#[derive(Debug, Args)]
pub struct OwnershipVerifyCommand {
    #[arg(help = "A file containing a binary ownership config block")]
    input: PathBuf,
    #[arg(
        short,
        long,
        help = "File containing the ECDSA public key to verify against"
    )]
    ecdsa_pub_key: Option<PathBuf>,
    #[arg(long, help = "File containing the SPX public key to verify against")]
    spx_pub_key: Option<PathBuf>,
    #[arg(long, help = "File containing the detached ECDSA signature")]
    ecdsa_sig: Option<PathBuf>,
    #[arg(long, help = "File containing the detached SPX signature")]
    spx_sig: Option<PathBuf>,
    #[arg(long, default_value_t = SphincsPlus::Sha2128sSimple, help = "SPX algorithm")]
    spx_algorithm: SphincsPlus,
}

impl CommandDispatch for OwnershipVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let input = std::fs::read(&self.input)?;
        let mut cursor = std::io::Cursor::new(&input);
        let header = TlvHeader::read(&mut cursor)?;
        let parsed_config = OwnerBlock::read(&mut cursor, header)?;

        if !parsed_config.ownership_key_alg.is_ecdsa() && !parsed_config.ownership_key_alg.is_spx()
        {
            return Err(anyhow!(
                "Unsupported verification algorithm: {}",
                parsed_config.ownership_key_alg
            ));
        }

        // Digest over the TBS section of the config.
        let digest = Sha256Digest::hash(&input[..OwnerBlock::SIGNATURE_OFFSET]);

        if parsed_config.ownership_key_alg.is_ecdsa() {
            let ecdsa_key: EcdsaPublicKey = if let Some(key_file) = &self.ecdsa_pub_key {
                EcdsaPublicKey::load(key_file)?
            } else {
                let pubk = match parsed_config.owner_key {
                    KeyMaterial::Ecdsa(ref raw_key) => raw_key,
                    KeyMaterial::Hybrid(ref hybrid) => &hybrid.ecdsa,
                    _ => return Err(anyhow!("Owner key material does not contain an ECDSA key!")),
                };
                pubk.try_into()?
            };

            let ecdsa_sig = if parsed_config.ownership_key_alg == OwnershipKeyAlg::EcdsaP256 {
                parsed_config.signature.clone()
            } else {
                let sig_file = self.ecdsa_sig.as_ref().ok_or_else(|| {
                    anyhow!("Algorithm {} requires a detached ECDSA signature, please provide --ecdsa-sig", parsed_config.ownership_key_alg)
                })?;
                EcdsaRawSignature::read_from_file(sig_file)?
            };
            ecdsa_key.verify(&digest, &ecdsa_sig)?;
        }

        if parsed_config.ownership_key_alg.is_spx() {
            let spx_key = if let Some(key_file) = &self.spx_pub_key {
                SpxPublicKey::read_pem_file(key_file)?
            } else {
                let pubk = match parsed_config.owner_key {
                    KeyMaterial::Spx(ref raw_key) => raw_key,
                    KeyMaterial::Hybrid(ref hybrid) => &hybrid.spx,
                    _ => return Err(anyhow!("Owner key material does not contain an SPX key!")),
                };
                let mut key_bytes = Vec::new();
                pubk.write(&mut key_bytes)?;
                SpxPublicKey::from_bytes(self.spx_algorithm, &key_bytes)?
            };

            let sig_file = self.spx_sig.as_ref().ok_or_else(|| {
                anyhow!(
                    "Algorithm {} requires a detached SPX signature, please provide --spx-sig",
                    parsed_config.ownership_key_alg
                )
            })?;
            let spx_sig_bytes = SpxRawSignature::read_from_file(sig_file, self.spx_algorithm)?;

            let (domain, msg) = if parsed_config.ownership_key_alg.is_prehashed() {
                (SpxDomain::PreHashedSha256, digest.as_ref())
            } else {
                (SpxDomain::Pure, &input[..OwnerBlock::SIGNATURE_OFFSET])
            };

            spx_key.verify(domain, spx_sig_bytes.as_bytes(), msg)?;
        }

        Ok(None)
    }
}

/// Compute digest command.
#[derive(Debug, Args)]
pub struct OwnershipDigestCommand {
    #[arg(help = "binary ownership config block")]
    input: PathBuf,
    /// Filename for an output bin file.
    #[arg(short, long)]
    bin: Option<PathBuf>,
}

/// Response format for the digest command.
#[derive(serde::Serialize, Annotate)]
pub struct OwnershipDigestResponse {
    #[annotate(comment = "SHA256 Digest excluding the signature and seal bytes", format = hexstr)]
    pub digest: Sha256Digest,
}

impl CommandDispatch for OwnershipDigestCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let input = std::fs::read(&self.input)?;
        let digest = Sha256Digest::hash(&input[..OwnerBlock::SIGNATURE_OFFSET]);

        if let Some(bin) = &self.bin {
            let mut file = File::create(bin)?;
            file.write_all(digest.as_ref())?;
        }
        Ok(Some(Box::new(OwnershipDigestResponse { digest })))
    }
}

#[derive(Debug, Args)]
pub struct OwnershipDetachedSignatureCommand {
    #[arg(short, long)]
    command: DetachedSignatureCommand,
    #[arg(long)]
    key_alg: OwnershipKeyAlg,
    #[arg(short, long)]
    nonce: u64,
    #[arg(long)]
    ecdsa_sig: Option<PathBuf>,
    #[arg(long)]
    spx_sig: Option<PathBuf>,
    /// Filename for an output detached signature bin file.
    output: PathBuf,
}

impl CommandDispatch for OwnershipDetachedSignatureCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let detatch_sig = DetachedSignature::from_raw_signatures(
            self.command.into(),
            self.key_alg,
            self.nonce,
            self.ecdsa_sig.as_deref(),
            self.spx_sig.as_deref(),
        )?;

        let mut file = File::create(&self.output)?;
        detatch_sig.write(&mut file)?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum OwnershipCommand {
    Config(OwnershipConfigCommand),
    Activate(OwnershipActivateCommand),
    Unlock(OwnershipUnlockCommand),
    Verify(OwnershipVerifyCommand),
    Digest(OwnershipDigestCommand),
    DetachedSignature(OwnershipDetachedSignatureCommand),
}
