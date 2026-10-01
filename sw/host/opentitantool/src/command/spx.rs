// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::crypto::spx;
use opentitanlib::crypto::spx::{SpxKeyFormat, SpxKeyLoadingMode};
use sphincsplus::{SphincsPlus, SpxPublicKey, SpxRawSignature, SpxSecretKey, SpxSignatureMode};

#[derive(Annotate, serde::Serialize)]
pub struct SpxPublicKeyInfo {
    pub algorithm: String,
    pub public_key_num_bits: usize,
    #[annotate(format=hex,comment="Words in little endian order")]
    pub public_key: Vec<u32>,
    #[annotate(comment = "Formatted for use in OTP configuration")]
    pub otp_encoded: String,
}

/// Show public information of a SPHINCS+ / SLH-DSA public or private key.
#[derive(Debug, Args)]
pub struct SpxKeyShowCommand {
    /// SPHINCS+ / SLH-DSA key file
    key_file: PathBuf,
}

impl CommandDispatch for SpxKeyShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let key = spx::load_spx_public_key(&self.key_file, SpxKeyLoadingMode::Fallback)?;
        let bytes = key.as_bytes();

        // The OTP creation tool is written in python and parses arbitrary
        // sized integers using python's `int` constructor and then writes
        // the values into the OTP image as little-endian values.
        //
        // We want to store into OTP the natural representation of the
        // SPHINCS+ / SLH-DSA key. Since the value is parsed by the `int`
        // constructor is interpreted as a big-endian integer, but written
        // into OTP in little-endian byte order, we want to reverse the
        // byte representation of the key for the OTP creation tool.
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

/// Describes the SPHINCS+ / SLH-DSA key files written by commands.
#[derive(Annotate, serde::Serialize)]
pub struct SpxKeyFileInfo {
    pub algorithm: String,
    pub format: String,
    pub private_key: Option<String>,
    pub public_key: Option<String>,
}

/// Generate a SPHINCS+ / SLH-DSA public & private key pair. The private key will
/// be written to <OUTPUT_DIR>/<BASENAME>.<EXT> and the public key will be
/// written to <OUTPUT_DIR>/<BASENAME>.pub.<EXT>, where <EXT> is determined
/// by the given format.
#[derive(Debug, Args)]
pub struct SpxKeyGenerateCommand {
    /// SPHINCS+ / SLH-DSA parameter set (SHA2-128s-simple, SHAKE-128s-simple)
    #[arg(long, default_value = "SHA2-128s-simple")]
    algorithm: SphincsPlus,
    /// Key encoding format
    #[arg(long, default_value_t = SpxKeyFormat::default())]
    format: SpxKeyFormat,
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
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let (private_key, public_key) = SpxSecretKey::new_keypair(self.algorithm)?;
        let mut file = self.output_dir.to_owned();
        file.push(&self.basename);
        file.set_extension(self.format.ext());
        spx::save_spx_private_key(&private_key, &file, self.format)?;
        let private_path = file.clone();

        file.set_extension(self.format.pub_ext());
        spx::save_spx_public_key(&public_key, &file, self.format)?;

        Ok(Some(Box::new(SpxKeyFileInfo {
            algorithm: self.algorithm.to_string(),
            format: self.format.to_string(),
            private_key: Some(private_path.to_string_lossy().into_owned()),
            public_key: Some(file.to_string_lossy().into_owned()),
        })))
    }
}

/// Convert a SPHINCS+ / SLH-DSA key to a different encoding format.
#[derive(Debug, Args)]
pub struct SpxKeyConvertCommand {
    /// Key encoding format to convert to
    #[arg(long, default_value_t = SpxKeyFormat::default())]
    format: SpxKeyFormat,
    /// Convert to a public key, regardless of whether the input file is a private key or not.
    #[arg(long)]
    public: bool,
    /// The SPHINCS+ / SLH-DSA key file to convert.
    input: PathBuf,
    /// Output key file.
    output: PathBuf,
}

impl CommandDispatch for SpxKeyConvertCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        if let Ok(private_key) = spx::load_spx_private_key(&self.input) {
            let (private_path, public_path) = if self.public {
                let public_key = SpxPublicKey::from(&private_key);
                spx::save_spx_public_key(&public_key, self.output.clone(), self.format)?;
                (None, Some(self.output.to_string_lossy().into_owned()))
            } else {
                spx::save_spx_private_key(&private_key, &self.output, self.format)?;
                (Some(self.output.to_string_lossy().into_owned()), None)
            };
            return Ok(Some(Box::new(SpxKeyFileInfo {
                algorithm: private_key.algorithm().to_string(),
                format: self.format.to_string(),
                private_key: private_path,
                public_key: public_path,
            })));
        }
        let pk = spx::load_spx_public_key(self.input.clone(), SpxKeyLoadingMode::PublicOnly)
            .context(format!(
                "{:?} was not recognized as a valid public or private key",
                self.input
            ))?;
        spx::save_spx_public_key(&pk, &self.output, self.format)?;
        Ok(Some(Box::new(SpxKeyFileInfo {
            algorithm: pk.algorithm().to_string(),
            format: self.format.to_string(),
            private_key: None,
            public_key: Some(self.output.to_string_lossy().into_owned()),
        })))
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum SpxKeySubcommands {
    Show(SpxKeyShowCommand),
    Generate(SpxKeyGenerateCommand),
    Convert(SpxKeyConvertCommand),
}

#[derive(serde::Serialize, Annotate)]
pub struct SpxSignResult {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub signature: Vec<u8>,
}

#[derive(Debug, Args)]
pub struct SpxSignCommand {
    /// Set to true if signing for a target that uses a byte-reversed representation of the hash.
    #[arg(short='r', long, action = clap::ArgAction::Set, default_value = "false")]
    spx_hash_reversal_bug: bool,
    /// The SPHINCS+ / SLH-DSA signature mode (Pure, PreHashedSha256)
    #[arg(long, default_value_t = SpxSignatureMode::default())]
    domain: SpxSignatureMode,
    /// The filename for the message to sign.
    message: PathBuf,
    /// The file containing the SPHINCS+ / SLH-DSA raw private key in a PEM or DER format.
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
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let mut message = std::fs::read(&self.message)?;
        if self.spx_hash_reversal_bug {
            message.reverse();
        }
        let private_key = spx::load_spx_private_key(&self.private_key)?;
        let signature = private_key.sign(self.domain.into(), &message)?;
        if let Some(output) = &self.output {
            std::fs::write(output, &signature)?;
            return Ok(None);
        }
        Ok(Some(Box::new(SpxSignResult { signature })))
    }
}

#[derive(Debug, Args)]
pub struct SpxVerifyCommand {
    /// Set to true if verifying for a target that uses a byte-reversed representation of the hash.
    #[arg(short='r', long, action = clap::ArgAction::Set, default_value = "false")]
    spx_hash_reversal_bug: bool,
    /// The SPHINCS+ / SLH-DSA signature mode (Pure, PreHashedSha256)
    #[arg(long, default_value_t = SpxSignatureMode::default())]
    domain: SpxSignatureMode,
    /// The signature algorithm (SHA2-128s-simple, SHAKE-128s-simple)
    #[arg(long, default_value = "SHA2-128s-simple")]
    spx_algorithm: SphincsPlus,
    /// The file containing the SPHINCS+ / SLH-DSA public key.
    #[arg(value_name = "KEY")]
    public_key: PathBuf,
    /// Message file to verify the signature against.
    message: PathBuf,
    /// SPHINCS+ / SLH-DSA signature file to verify (raw binary).
    signature: PathBuf,
}

impl CommandDispatch for SpxVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let mut message = std::fs::read(&self.message)?;
        if self.spx_hash_reversal_bug {
            message.reverse();
        }
        let public_key = spx::load_spx_public_key(&self.public_key, SpxKeyLoadingMode::PublicOnly)?;
        let signature = SpxRawSignature::read_from_file(&self.signature, self.spx_algorithm)?;
        public_key.verify(self.domain.into(), signature.as_bytes(), &message)?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// SPHINCS+ / SLH-DSA commands.
#[allow(clippy::large_enum_variant)]
pub enum Spx {
    #[command(subcommand)]
    /// Commands for interacting with & manipulating SPHINCS+ / SLH-DSA keys.
    Key(SpxKeySubcommands),
    /// Sign a message using SPHINCS+ / SLH-DSA.
    Sign(SpxSignCommand),
    /// Verify a signature using SPHINCS+ / SLH-DSA.
    Verify(SpxVerifyCommand),
}
