// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::{Path, PathBuf};

use ml_dsa::{Generate, Keypair, MlDsa44, MlDsa65, MlDsa87, SigningKey};
use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::crypto::mldsa::{
    MldsaKeyFormat, MldsaParameterSet, MldsaPkcs8Params, mldsa_key_from_der,
    mldsa_parameter_set_from_der, read_mldsa_key_file, save_mldsa_private_key,
    save_mldsa_public_key,
};

/// Calls the generic function `$f` instantiated for the ML-DSA `$parameter_set`.
macro_rules! with_mldsa_params {
    ($parameter_set:expr, $f:ident($($arg:expr),* $(,)?)) => {
        match $parameter_set {
            MldsaParameterSet::Mldsa44 => $f::<MlDsa44>($($arg),*),
            MldsaParameterSet::Mldsa65 => $f::<MlDsa65>($($arg),*),
            MldsaParameterSet::Mldsa87 => $f::<MlDsa87>($($arg),*),
        }
    };
}

#[derive(Annotate)]
pub struct MldsaPublicKeyInfo {
    pub parameter_set: String,
    pub public_key_num_bits: usize,
    #[annotate(format=hex, comment="Words in little endian order.")]
    pub public_key: Vec<u32>,
}

/// Show public information of an ML-DSA public or private key.
#[derive(Debug, Args)]
pub struct MldsaKeyShowCommand {
    /// ML-DSA key file (PEM or DER).
    key_file: PathBuf,
}

/// Returns the encoded public key of the DER encoding of an ML-DSA public or private key.
fn public_key_bytes<P: MldsaPkcs8Params>(der: &[u8]) -> Result<Vec<u8>> {
    let (key, _) = mldsa_key_from_der::<P>(der)?;
    Ok(key.encode().to_vec())
}

impl CommandDispatch for MldsaKeyShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let doc = read_mldsa_key_file(&self.key_file)?;
        let parameter_set = mldsa_parameter_set_from_der(doc.as_bytes())?;
        let bytes = with_mldsa_params!(parameter_set, public_key_bytes(doc.as_bytes()))?;
        Ok(Some(Box::new(MldsaPublicKeyInfo {
            parameter_set: parameter_set.to_string(),
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
    #[arg(long, alias = "algorithm", default_value_t = MldsaParameterSet::Mldsa87)]
    parameter_set: MldsaParameterSet,
    /// Key encoding format (pem or pkcs8-pem, der or pkcs8-der)
    #[arg(long, default_value_t = MldsaKeyFormat::default())]
    format: MldsaKeyFormat,
    /// Output directory.
    output_dir: PathBuf,
    /// Basename for the generated key pair.
    basename: String,
}

/// Generates an ML-DSA key pair and writes it to the given files.
fn generate_key<P: MldsaPkcs8Params>(
    private_path: &Path,
    public_path: &Path,
    format: MldsaKeyFormat,
) -> Result<()> {
    let private_key = SigningKey::<P>::try_generate()?;
    save_mldsa_private_key(&private_key, private_path, format)?;
    save_mldsa_public_key(&private_key.verifying_key(), public_path, format)
}

impl CommandDispatch for MldsaKeyGenerateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let private_path = self
            .output_dir
            .join(format!("{}.{}", self.basename, self.format.ext()));
        let public_path =
            self.output_dir
                .join(format!("{}.{}", self.basename, self.format.pub_ext()));

        with_mldsa_params!(
            self.parameter_set,
            generate_key(&private_path, &public_path, self.format)
        )?;

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
