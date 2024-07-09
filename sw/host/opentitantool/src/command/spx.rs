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
use sphincsplus::{DecodeKey, EncodeKey, SphincsPlus, SpxDomain, SpxPublicKey, SpxSecretKey};

#[derive(Annotate, serde::Serialize)]
pub struct SpxPublicKeyInfo {
    pub algorithm: String,
    pub public_key_num_bits: usize,
    #[annotate(format=hex,comment="Words in little endian order.")]
    pub public_key: Vec<u32>,
    #[annotate(comment = "Formatted for use in OTP configuration")]
    pub otp_encoded: String,
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
        let key = SpxPublicKey::read_pem_file(&self.key_file)?;
        let bytes = key.as_bytes();

        // The OTP creation tool is written in python and parses arbitrary
        // sized integers using python's `int` constructor and then writes
        // the values into the OTP image as little-endian values.
        //
        // We want to store into OTP the natuaral representaion of the
        // SPHINCS+ key.  Since the value is parsed by the `int` constructor
        // is interpreted as a big-endian integer, but written into OTP in
        // little-endian byte order, we want to reverse the byte representation
        // of the key for the OTP creation tool.
        let mut otp = bytes.to_vec();
        otp.reverse();
        let otp = format!("0x{}", hex::encode(otp));

        Ok(Some(Box::new(SpxPublicKeyInfo {
            algorithm: key.algorithm().to_string(),
            public_key_num_bits: bytes.len() * 8,
            public_key: bytes
                .chunks(4)
                .map(|x| u32::from_le_bytes(x.try_into().unwrap()))
                .collect(),
            otp_encoded: otp,
        })))
    }
}

/// Generate a SPHINCS+-SHAKE256-128s-simple public private key pair. The full keypair will be
/// written to <OUTPUT_DIR>/<BASENAME>.key and the public key will be written to
/// <OUTPUT_DIR>/<BASENAME>.pub.key.
#[derive(Debug, Args)]
pub struct SpxKeyGenerateCommand {
    /// SPHINCS+ algorithm (SHAKE-128s-simple, SHA2-128s-simple)
    #[arg(long, default_value = "SHAKE-128s-simple")]
    algorithm: SphincsPlus,
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
        let (private_key, public_key) = SpxSecretKey::new_keypair(self.algorithm)?;
        let mut file = self.output_dir.to_owned();
        file.push(&self.basename);
        file.set_extension("pem");
        private_key.write_pem_file(&file)?;

        file.set_extension("pub.pem");
        public_key.write_pem_file(&file)?;

        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum SpxKeySubcommands {
    Show(SpxKeyShowCommand),
    Generate(SpxKeyGenerateCommand),
}

#[derive(serde::Serialize, Annotate)]
pub struct SpxSignResult {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub signature: Vec<u8>,
}

#[derive(Debug, Args)]
pub struct SpxSignCommand {
    /// The signature domain (Raw, Pure, PreHashedSha256)
    #[arg(long, default_value_t = SpxDomain::default())]
    domain: SpxDomain,
    /// The filename for the message to sign.
    message: PathBuf,
    /// The file containing the SPHINCS+ raw private key in PEM format.
    #[arg(value_name = "KEY_FILE")]
    private_key: PathBuf,
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
        let private_key = SpxSecretKey::read_pem_file(&self.private_key)?;
        let signature = private_key.sign(self.domain, &message)?;
        if let Some(output) = &self.output {
            std::fs::write(output, &signature)?;
            return Ok(None);
        }
        Ok(Some(Box::new(SpxSignResult { signature })))
    }
}

#[derive(Debug, Args)]
pub struct SpxVerifyCommand {
    /// The signature domain (Raw, Pure, PreHashedSha256)
    #[arg(long, default_value_t = SpxDomain::default())]
    domain: SpxDomain,
    /// The file containing the SPHINCS+ raw public key in PEM format.
    #[arg(value_name = "KEY")]
    public_key: PathBuf,
    /// Message file to verify the signature against.
    message: PathBuf,
    /// SPHINCS+ signature file to verify (raw binary).
    signature: PathBuf,
}

impl CommandDispatch for SpxVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let message = std::fs::read(&self.message)?;
        let public_key = SpxPublicKey::read_pem_file(&self.public_key)?;
        let signature = std::fs::read(&self.signature)?;
        public_key.verify(self.domain, &signature, &message)?;
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
