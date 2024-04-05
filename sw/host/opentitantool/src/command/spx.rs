// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::spx::{self, SpxKeypair, SpxPublicKeyPart, SpxSignature};
use opentitanlib::util::file::{FromReader, PemSerilizable, ToWriter};

#[derive(Annotate, serde::Serialize)]
pub struct SpxPublicKeyInfo {
    pub public_key_num_bits: usize,
    #[annotate(format=hex,comment="Words in little endian order.")]
    pub public_key: Vec<u32>,
}

/// Show public information of a SPHINCS+ public key or key pair.
#[derive(Debug, Args)]
pub struct SpxKeyShowCommand {
    /// SPHINCS+ key file (either just the public key or full keypair).
    key_file: PathBuf,
}

impl CommandDispatch for SpxKeyShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let key = spx::load_spx_key(&self.key_file)?;

        Ok(Some(Box::new(SpxPublicKeyInfo {
            public_key_num_bits: key.pk_len() * 8,
            public_key: key
                .pk_as_bytes()
                .chunks(4)
                .map(|x| u32::from_le_bytes(x.try_into().unwrap()))
                .collect(),
        })))
    }
}

/// Generate a SPHINCS+-SHAKE256-128s-simple public private key pair. The full keypair will be
/// written to <OUTPUT_DIR>/<BASENAME>.key and the public key will be written to
/// <OUTPUT_DIR>/<BASENAME>.pub.key.
#[derive(Debug, Args)]
pub struct SpxKeyGenerateCommand {
    /// Output directory.
    output_dir: PathBuf,
    /// Basename for the generated key pair.
    basename: String,
}

impl CommandDispatch for SpxKeyGenerateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let private_key = SpxKeypair::generate();
        let mut file = self.output_dir.to_owned();
        file.push(&self.basename);
        file.set_extension("pem");
        private_key.write_pem_file(&file)?;

        file.set_extension("pub.pem");
        private_key.into_public_key().write_pem_file(&file)?;

        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum SpxKeySubcommands {
    Show(SpxKeyShowCommand),
    Generate(SpxKeyGenerateCommand),
}

#[derive(serde::Serialize)]
pub struct SpxSignResult {
    pub signature: String,
}

#[derive(Debug, Args)]
pub struct SpxSignCommand {
    /// The filename for the message to sign.
    message: PathBuf,

    /// The file contianing SPHICS+ keypair.
    #[arg(value_name = "KEY_FILE")]
    keypair: PathBuf,
    /// The filename to write the signature to.
    #[arg(short, long)]
    output: Option<PathBuf>,
}

impl CommandDispatch for SpxSignCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let message = std::fs::read(&self.message)?;
        let keypair = SpxKeypair::read_pem_file(&self.keypair)?;
        let signature = keypair.sign(&message);
        if let Some(output) = &self.output {
            signature.write_to_file(output)?;
            return Ok(None);
        }
        Ok(Some(Box::new(SpxSignResult {
            signature: signature.to_string(),
        })))
    }
}

#[derive(Debug, Args)]
pub struct SpxVerifyCommand {
    /// Key file.
    #[arg(value_name = "KEY")]
    key_file: PathBuf,
    /// Message file to verify the signature against.
    message: PathBuf,
    /// SPHINCS+ signature file to verify.
    signature: PathBuf,
}

impl CommandDispatch for SpxVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let message = std::fs::read(&self.message)?;
        let keypair = spx::load_spx_key(&self.key_file)?;
        let signature = SpxSignature::read_from_file(&self.signature)?;
        keypair.verify(&message, &signature)?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// SPHICS+ commands.
#[allow(clippy::large_enum_variant)]
pub enum Spx {
    #[command(subcommand)]
    Key(SpxKeySubcommands),
    Sign(SpxSignCommand),
    Verify(SpxVerifyCommand),
}
