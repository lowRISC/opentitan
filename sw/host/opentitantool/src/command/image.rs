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

use opentitanlib::crypto::rsa::{Modulus, RsaPrivateKey, RsaPublicKey, Signature as RsaSignature};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::crypto::spx::{self, SpxKey, SpxPublicKey, SpxPublicKeyPart, SpxSignature};
use opentitanlib::image::image::{self, ImageAssembler};
use opentitanlib::image::manifest_def::ManifestSpec;
use opentitanlib::util::file::{FromReader, ToWriter};
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
        std::fs::write(&self.output, content)?;
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

    #[structopt(long, help = "Filename for an external RSA signature file")]
    rsa_signature: Option<PathBuf>,
    #[structopt(short, long, help = "Filename for an external SPHINCS+ signature file")]
    spx_signature: Option<PathBuf>,
    #[structopt(
        long,
        help = "Filename for the RSA PKCS8 key corresponding to the signature",
        long_help = "Passing a private key indicates the key will be used for signing."
    )]
    rsa_key: Option<PathBuf>,
    #[structopt(
        long,
        help = "Filename for the SPHINCS+ key corresponding to the signature",
        long_help = "Passing a private key indicates the key will be used for signing."
    )]
    spx_key: Option<PathBuf>,
    #[structopt(
        short,
        long,
        help = "Filename to write the output to instead of updating the input file"
    )]
    output: Option<PathBuf>,
}

fn load_rsa_key(key_file: &Path) -> Result<(RsaPublicKey, Option<RsaPrivateKey>)> {
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
            let def = ManifestSpec::read_from_file(manifest)?;
            image.overwrite_manifest(def)?;
        }

        // Update the public key fields of the manifest before signing the image. Otherwise we have
        // to repeat the first signing operation.
        let mut rsa_private_key: Option<RsaPrivateKey> = None;
        if let Some(key) = &self.rsa_key {
            let (public, private) = load_rsa_key(key)?;
            image.update_modulus(public.modulus())?;
            if let Some(private) = private {
                rsa_private_key = Some(private);
            }
        }
        let mut spx_private_key: Option<SpxKey> = None;
        if let Some(key) = &self.spx_key {
            let key = spx::load_spx_key(key)?;
            image.update_spx_key(&key)?;
            if let SpxKey::Private(private) = key {
                spx_private_key = Some(SpxKey::Private(private));
            }
        }

        // Update `signed_area_end` after adding all the signed extensions.
        image.update_signed_region()?;

        // Sign the image
        if let Some(key) = rsa_private_key {
            image.update_rsa_signature(key.sign(&image.compute_digest())?)?;
        }
        if let Some(SpxKey::Private(key)) = spx_private_key {
            image.update_spx_signature(image.map_signed_region(|buf| key.sign(buf)).0)?;
        }

        if let Some(rsa_signature) = &self.rsa_signature {
            let signature = RsaSignature::read_from_file(rsa_signature)?;
            image.update_rsa_signature(signature)?;
        }

        if let Some(spx_signature) = &self.spx_signature {
            let signature = SpxSignature::read_from_file(spx_signature)?;
            image.update_spx_signature(signature.0)?;
        }

        image.write_to_file(self.output.as_ref().unwrap_or(&self.image))?;
        Ok(None)
    }
}

/// Manifest verify command.
#[derive(Debug, StructOpt)]
pub struct ManifestVerifyCommand {
    #[structopt(name = "IMAGE", help = "Filename for the image to verify")]
    image: PathBuf,
    #[structopt(short, long, help = "Run verification for SPHINCS+")]
    spx: bool,
}

impl CommandDispatch for ManifestVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = image::Image::read_from_file(&self.image)?;
        let manifest: ManifestSpec = image.borrow_manifest()?.try_into()?;

        // Verify RSA signature.
        let rsa_modulus = manifest
            .rsa_modulus()
            .ok_or_else(|| anyhow!("Invalid RSA modulus"))?;
        let rsa_sig = manifest
            .rsa_signature()
            .ok_or_else(|| anyhow!("Invalid RSA signature"))?;
        let digest = Sha256Digest::from_le_bytes(image.compute_digest().to_le_bytes())?;
        let rsa_key = RsaPublicKey::new(Modulus::from_le_bytes(rsa_modulus.to_le_bytes())?)?;
        let rsa_sig = RsaSignature::from_le_bytes(rsa_sig.to_le_bytes())?;
        rsa_key.verify(&digest, &rsa_sig)?;

        if self.spx {
            let spx_key = manifest
                .spx_key()
                .ok_or_else(|| anyhow!("Invalid SPHINCS+ key"))?;
            let spx_sig = manifest
                .spx_signature()
                .ok_or_else(|| anyhow!("Invalid SPHINCS+ signature"))?;

            let spx_sig = SpxSignature(spx::Signature::from_le_bytes(spx_sig.to_le_bytes())?);
            let spx_key = SpxPublicKey::from_bytes(&spx_key.to_be_bytes())?;
            image.map_signed_region(|m| spx_key.verify(m, &spx_sig))?;
        }

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
#[derive(serde::Serialize, Annotate)]
pub struct DigestResponse {
    #[serde(with = "serde_bytes")]
    #[annotate(comment = "SHA256 Digest excluding the image signature bytes", format = hexstr)]
    pub digest: Vec<u8>,
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
            file.write_all(&digest.to_le_bytes())?;
        }
        Ok(Some(Box::new(DigestResponse {
            digest: digest.to_be_bytes(),
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
