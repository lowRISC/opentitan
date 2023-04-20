// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::{Path, PathBuf};
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::spx::{SpxKeypair, SpxPublicKey, SpxPublicKeyPart, SpxSignature};
use opentitanlib::image::image::Image;
use opentitanlib::util::file::{FromReader, PemSerilizable, ToWriter};

/// Given the path to a public key, returns the public key. Given
/// the path to a full keypair, extracts the public key from the private
/// key and returns the public key.
fn load_pub_or_priv_key(path: &Path) -> Result<SpxPublicKey> {
    Ok(match SpxPublicKey::read_pem_file(path) {
        Ok(pk) => pk,
        Err(e1) => match SpxKeypair::read_pem_file(path) {
            Ok(kp) => kp.into_public_key(),
            Err(e2) => {
                return Err(anyhow!(
                    "\n\
                        Reading as public key: {}\n\
                        Reading as keypair: {}",
                    e1,
                    e2
                ))
            }
        },
    })
}

#[derive(Annotate, serde::Serialize)]
pub struct SpxPublicKeyInfo {
    pub public_key_num_bits: usize,
    #[annotate(format=hex)]
    pub public_key: Vec<u8>,
}

/// Show public information of a SPHINCS+ public key or key pair.
#[derive(Debug, StructOpt)]
pub struct SpxKeyShowCommand {
    #[structopt(
        name = "KEY_FILE",
        help = "SPHINCS+ key file (either just the public key or full keypair)"
    )]
    key_file: PathBuf,
}

impl CommandDispatch for SpxKeyShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let key = load_pub_or_priv_key(&self.key_file)?;

        Ok(Some(Box::new(SpxPublicKeyInfo {
            public_key_num_bits: key.pk_len() * 8,
            public_key: key.pk_as_bytes().to_vec(),
        })))
    }
}

/// Generate a SPHINCS+-SHAKE256-128s-simple public private key pair. The full keypair will be
/// written to <OUTPUT_DIR>/<BASENAME>.key and the public key will be written to
/// <OUTPUT_DIR>/<BASENAME>.pub.key.
#[derive(Debug, StructOpt)]
pub struct SpxKeyGenerateCommand {
    #[structopt(name = "OUTPUT_DIR", help = "Output directory")]
    output_dir: PathBuf,
    #[structopt(name = "BASENAME", help = "Basename for the generated key pair")]
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

#[derive(Debug, StructOpt, CommandDispatch)]
pub enum SpxKeySubcommands {
    Show(SpxKeyShowCommand),
    Generate(SpxKeyGenerateCommand),
}

#[derive(serde::Serialize)]
pub struct SpxSignResult {
    pub signature: String,
}

#[derive(Debug, StructOpt)]
pub struct SpxSignCommand {
    #[structopt(name = "IMAGE", help = "The filename for the image to sign")]
    image: PathBuf,

    #[structopt(name = "KEY_FILE", help = "The file contianing SPHICS+ keypair")]
    keypair: PathBuf,
    #[structopt(short, long, help = "The filename to write the signature to")]
    output: Option<PathBuf>,
}

impl CommandDispatch for SpxSignCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = Image::read_from_file(&self.image)?;
        let keypair = SpxKeypair::read_pem_file(&self.keypair)?;
        let signature = image.map_signed_region(|b| keypair.sign(b));
        if let Some(output) = &self.output {
            signature.clone().write_to_file(output)?;
        }
        Ok(Some(Box::new(SpxSignResult {
            signature: signature.to_string(),
        })))
    }
}

#[derive(Debug, StructOpt)]
pub struct SpxVerifyCommand {
    #[structopt(name = "KEY", help = "Key file")]
    key_file: PathBuf,
    #[structopt(name = "IMAGE", help = "Image file to verify the signature against")]
    image: PathBuf,
    #[structopt(name = "SIGNATURE", help = "SPHINCS+ signature file to verify")]
    signature: PathBuf,
}

impl CommandDispatch for SpxVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = Image::read_from_file(&self.image)?;
        let keypair = load_pub_or_priv_key(&self.key_file)?;
        let signature = SpxSignature::read_from_file(&self.signature)?;
        image.map_signed_region(|b| keypair.verify(b, &signature))?;
        Ok(None)
    }
}

#[derive(Debug, StructOpt, CommandDispatch)]
/// SPHICS+ commands.
#[allow(clippy::large_enum_variant)]
pub enum Spx {
    Key(SpxKeySubcommands),
    Sign(SpxSignCommand),
    Verify(SpxVerifyCommand),
}
