// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use mldsa::{
    DecodeKey, EncodeKey, KeyFormat, MldsaError, MldsaParameterSet, MldsaPublicKey, MldsaSecretKey,
};
use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;

#[derive(Annotate)]
pub struct MldsaPublicKeyInfo {
    pub parameter_set: String,
    pub public_key_num_bits: usize,
    #[annotate(format=hex,comment="Words in little endian order.")]
    pub public_key: Vec<u32>,
}

/// Show public information of an ML-DSA public or private key.
#[derive(Debug, Args)]
pub struct MldsaKeyShowCommand {
    /// ML-DSA key file (PEM or DER).
    key_file: PathBuf,
}

impl CommandDispatch for MldsaKeyShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let key = match MldsaPublicKey::from_file(&self.key_file) {
            Ok(key) => key,
            Err(MldsaError::Io(e)) => return Err(e.into()),
            // Maybe it is a private key, derive the public key from it.
            Err(_) => MldsaSecretKey::from_file(&self.key_file)?.public_key(),
        };
        let bytes = key.as_bytes();
        Ok(Some(Box::new(MldsaPublicKeyInfo {
            parameter_set: key.parameter_set().to_string(),
            public_key_num_bits: bytes.len() * 8,
            public_key: bytes
                .chunks(4)
                .map(|x| u32::from_le_bytes(x.try_into().unwrap()))
                .collect(),
        })))
    }
}

/// Describes the ML-DSA key files written by commands.
#[derive(Annotate)]
pub struct MldsaKeyFileInfo {
    pub parameter_set: String,
    pub format: String,
    pub private_key: String,
    pub public_key: String,
}

/// Generate an ML-DSA public and private key pair.
#[derive(Debug, Args)]
pub struct MldsaKeyGenerateCommand {
    /// ML-DSA-{44, 65, 87} parameter set.
    #[arg(long, default_value_t = MldsaParameterSet::Mldsa87)]
    parameter_set: MldsaParameterSet,
    /// Key encoding format (pem, der)
    #[arg(long, default_value_t = KeyFormat::default())]
    format: KeyFormat,
    /// Output directory.
    output_dir: PathBuf,
    /// Basename for the generated key pair.
    basename: String,
}

impl CommandDispatch for MldsaKeyGenerateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let private_key = MldsaSecretKey::generate(self.parameter_set)?;
        let private_path = self
            .output_dir
            .join(format!("{}.{}", self.basename, self.format.ext()));
        let public_path =
            self.output_dir
                .join(format!("{}.{}", self.basename, self.format.pub_ext()));

        private_key.write_file(&private_path, self.format)?;
        private_key
            .public_key()
            .write_file(&public_path, self.format)?;

        Ok(Some(Box::new(MldsaKeyFileInfo {
            parameter_set: self.parameter_set.to_string(),
            format: self.format.to_string(),
            private_key: private_path.to_string_lossy().into_owned(),
            public_key: public_path.to_string_lossy().into_owned(),
        })))
    }
}

/// Commands for interacting with ML-DSA keys.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum MldsaKeySubcommands {
    Show(MldsaKeyShowCommand),
    Generate(MldsaKeyGenerateCommand),
}

/// ML-DSA commands.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum Mldsa {
    #[command(subcommand)]
    Key(MldsaKeySubcommands),
}
