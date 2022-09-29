// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Result};
use serde_annotate::Annotate;
use std::any::Any;
use std::convert::TryInto;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

use opentitanlib::crypto::rsa::{Modulus, RsaPrivateKey, RsaPublicKey, Signature};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::image::image::{self, ImageAssembler};
use opentitanlib::image::manifest_def::ManifestSpec;
use opentitanlib::util::parse_int::ParseInt;

/// Bootstrap the target device.
#[derive(Debug, StructOpt)]
pub struct AssembleCommand {
    #[structopt(
        short,
        long,
        parse(try_from_str=usize::from_str),
        default_value="1048576",
        help="The size of the image to assemble"
    )]
    size: usize,
    #[structopt(
        short,
        long,
        parse(try_from_str),
        default_value = "true",
        help = "Whether or not the assembled image is mirrored"
    )]
    mirror: bool,
    #[structopt(short, long, help = "Filename to write the assembled image to")]
    output: PathBuf,
    #[structopt(
        name = "FILE",
        min_values(1),
        help = "One or more filename@offset specifiers to assemble into an image"
    )]
    filename: Vec<String>,
}

impl CommandDispatch for AssembleCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // The `min_values` structopt attribute should take care of this, but it doesn't.
        ensure!(
            !self.filename.is_empty(),
            "You must supply at least one filename"
        );
        let mut image = ImageAssembler::with_params(self.size, self.mirror);
        image.parse(&self.filename)?;
        let content = image.assemble()?;
        std::fs::write(&self.output, &content)?;
        Ok(None)
    }
}

/// Manifest show command.
#[derive(Debug, StructOpt)]
pub struct ManifestShowCommand {
    #[structopt(name = "IMAGE", help = "Filename for the image to display")]
    image: PathBuf,
}

impl CommandDispatch for ManifestShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = image::Image::read_from_file(&self.image)?;
        let manifest_def: ManifestSpec = image.borrow_manifest()?.try_into()?;
        Ok(Some(Box::new(manifest_def)))
    }
}

/// Manifest update command.
#[derive(Debug, StructOpt)]
pub struct ManifestUpdateCommand {
    #[structopt(name = "IMAGE", help = "Filename for the image to update")]
    image: PathBuf,
    #[structopt(
        short,
        long,
        help = "Filename for an HJSON configuration specifying manifest fields"
    )]
    manifest: Option<PathBuf>,

    #[structopt(long, help = "Sign the image with the given key_file")]
    sign: bool,
    #[structopt(short, long, help = "Filename for a signature file")]
    signature_file: Option<PathBuf>,
    #[structopt(
        short,
        long,
        help = "Filename for the key file corresponding to the signature"
    )]
    key_file: Option<PathBuf>,
    #[structopt(
        short,
        long,
        help = "Filename to write the output to instead of updating the input file"
    )]
    output: Option<PathBuf>,
}

fn load_key(key_file: &Path) -> Result<(RsaPublicKey, Option<RsaPrivateKey>)> {
    match RsaPublicKey::from_pkcs1_der_file(key_file) {
        Ok(key) => Ok((key, None)),
        Err(_) => match RsaPrivateKey::from_pkcs8_der_file(key_file) {
            Ok(key) => Ok((RsaPublicKey::from_private_key(&key), Some(key))),
            Err(e) => Err(e),
        },
    }
}

impl CommandDispatch for ManifestUpdateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let mut image = image::Image::read_from_file(&self.image)?;

        // Update the size field in the manifest to reflect the actual size of the image.
        image.update_length()?;

        // Apply the manifest values to the image.
        if let Some(manifest) = &self.manifest {
            let def = ManifestSpec::read_from_file(&manifest)?;
            image.overwrite_manifest(def)?;
        }

        if let Some(key_file) = &self.key_file {
            let (keypub, keypriv) = load_key(key_file)?;
            image.update_modulus(keypub.modulus())?;
            if self.sign {
                let private_key = keypriv.ok_or(anyhow!(
                    "The supplied key_file does not contain a private key"
                ))?;
                // Compute the digest over the image, sign it and update it.
                image.update_signature(private_key.sign(&image.compute_digest())?)?;
            }
        }

        if let Some(signature_file) = &self.signature_file {
            let signature = Signature::read_from_file(signature_file)?;
            image.update_signature(signature)?;
        }

        image.write_to_file(&self.output.as_ref().unwrap_or(&self.image))?;
        Ok(None)
    }
}

/// Manifest verify command.
#[derive(Debug, StructOpt)]
pub struct ManifestVerifyCommand {
    #[structopt(name = "IMAGE", help = "Filename for the image to verify")]
    image: PathBuf,
}

impl CommandDispatch for ManifestVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = image::Image::read_from_file(&self.image)?;
        let manifest: ManifestSpec = image.borrow_manifest()?.try_into()?;
        let modulus = manifest.modulus().ok_or(anyhow!("Invalid modulus"))?;
        let signature = manifest.signature().ok_or(anyhow!("Invalid signature"))?;
        let digest = Sha256Digest::from_le_bytes(image.compute_digest().to_le_bytes())?;
        let key = RsaPublicKey::new(Modulus::from_le_bytes(modulus.to_le_bytes())?)?;
        let signature = Signature::from_le_bytes(signature.to_le_bytes())?;
        key.verify(&digest, &signature)?;
        Ok(None)
    }
}

/// Compute digest command.
#[derive(Debug, StructOpt)]
pub struct DigestCommand {
    #[structopt(
        name = "IMAGE",
        help = "Filename for the image to calculate the digest for"
    )]
    image: PathBuf,
    #[structopt(short, long, help = "Filename for an output bin file")]
    bin: Option<PathBuf>,
}

/// Response format for the digest command.
#[derive(serde::Serialize)]
pub struct DigestResponse {
    pub digest: String,
}

impl CommandDispatch for DigestCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = image::Image::read_from_file(&self.image)?;
        let digest = image.compute_digest();
        if let Some(bin) = &self.bin {
            let mut file = File::create(bin)?;
            file.write(&digest.to_le_bytes())?;
        }
        Ok(Some(Box::new(DigestResponse {
            digest: format!("0x{}", hex::encode(&digest.to_be_bytes())),
        })))
    }
}

#[derive(Debug, StructOpt, CommandDispatch)]
/// Manifest manipulation commands.
pub enum ManifestCommand {
    Show(ManifestShowCommand),
    Update(ManifestUpdateCommand),
    Verify(ManifestVerifyCommand),
}

#[derive(Debug, StructOpt, CommandDispatch)]
/// Image manipulation commands.
pub enum Image {
    Assemble(AssembleCommand),
    Manifest(ManifestCommand),
    Digest(DigestCommand),
}
