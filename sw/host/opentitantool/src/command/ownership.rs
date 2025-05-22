// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Result};
use clap::{Args, Subcommand, ValueEnum};
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::helper::{OwnershipActivateParams, OwnershipUnlockParams};
use opentitanlib::crypto::ecdsa::{EcdsaPrivateKey, EcdsaPublicKey, EcdsaRawSignature};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::ownership::{
    DetachedSignature, DetachedSignatureCommand, GlobalFlags, KeyMaterial, OwnerBlock,
    OwnershipKeyAlg, TlvHeader,
};

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
            log::warn!("The algorithm {} requires a detached signature, but no detach signature file was specified.", self.params.algorithm);
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
            log::warn!("The algorithm {} requires a detached signature, but no detach signature file was specified.", self.params.algorithm);
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
        help = "File containing the public key to verfify against"
    )]
    signer_pub_key: Option<PathBuf>,
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

        match parsed_config.ownership_key_alg {
            OwnershipKeyAlg::EcdsaP256 => (),
            _ => {
                return Err(anyhow!(
                    "The only supported verification algorithm is ECDSA"
                ))
            }
        };

        let ecdsa_key: EcdsaPublicKey = if let Some(key_file) = &self.signer_pub_key {
            EcdsaPublicKey::load(key_file)?
        } else {
            // Retrieve the ECDSA key.
            let pubk = match parsed_config.owner_key {
                KeyMaterial::Ecdsa(ref raw_key) => raw_key,
                _ => return Err(anyhow!("Owner key material does not match key algorithm!")),
            };
            pubk.try_into()?
        };
        // Digest over the TBS section of the config.
        let digest = Sha256Digest::hash(&input[..OwnerBlock::SIGNATURE_OFFSET]);

        ecdsa_key.verify(&digest, &parsed_config.signature)?;
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
