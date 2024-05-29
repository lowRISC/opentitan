// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::collections::HashSet;
use std::convert::TryInto;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

use opentitanlib::crypto::ecdsa::{
    EcdsaPrivateKey, EcdsaPublicKey, EcdsaRawPublicKey, EcdsaRawSignature,
};
use opentitanlib::crypto::rsa::{RsaPrivateKey, RsaPublicKey, Signature as RsaSignature};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::crypto::spx::{self, SpxKey, SpxKeypair, SpxSignature};
use opentitanlib::image::image::{self, ImageAssembler};
use opentitanlib::image::manifest::{ManifestExtSpxSignature, ManifestKind};
use opentitanlib::image::manifest_def::ManifestSpec;
use opentitanlib::image::manifest_ext::{ManifestExtEntry, ManifestExtId, ManifestExtSpec};
use opentitanlib::util::file::{FromReader, ToWriter};
use opentitanlib::util::parse_int::ParseInt;

/// Bootstrap the target device.
#[derive(Debug, Args)]
pub struct AssembleCommand {
    /// The size of the image to assemble.
    #[arg(short, long, value_parser = usize::from_str, default_value="1048576")]
    size: usize,
    /// Whether or not the assembled image is mirrored.
    #[arg(short, long, action = clap::ArgAction::Set, default_value = "true")]
    mirror: bool,
    /// Filename to write the assembled image to.
    #[arg(short, long)]
    output: PathBuf,
    /// One or more filename@offset specifiers to assemble into an image.
    #[arg(value_name = "FILE", required = true, num_args = 0..)]
    filename: Vec<String>,
}

impl CommandDispatch for AssembleCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let mut image = ImageAssembler::with_params(self.size, self.mirror);
        // Filter out empty arguments that could appear e.g. because of bazel
        // and also trim extra spaces if necessary.
        let filenames = self
            .filename
            .iter()
            .map(|x| x.trim())
            .filter(|x| !x.is_empty())
            .collect::<Vec<_>>();
        if filenames.is_empty() {
            log::warn!("No filenames provided, will produce an empty image")
        }
        image.parse(&filenames)?;
        let content = image.assemble()?;
        std::fs::write(&self.output, content)?;
        Ok(None)
    }
}

/// Manifest show command.
#[derive(Debug, Args)]
pub struct ManifestShowCommand {
    /// Filename for the image to display.
    image: PathBuf,
}

#[derive(Debug, serde::Serialize, Annotate)]
pub struct ManifestShowResult {
    #[annotate(format=hex)]
    kind: ManifestKind,
    #[annotate(format=hex)]
    offset: usize,
    manifest: ManifestSpec,
}

impl CommandDispatch for ManifestShowCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = image::Image::read_from_file(&self.image)?;
        let result = image
            .subimages()?
            .iter()
            .map(|s| ManifestShowResult {
                kind: s.kind,
                offset: s.offset,
                manifest: s.manifest.try_into().expect("manifest conversion"),
            })
            .collect::<Vec<_>>();
        Ok(Some(Box::new(result)))
    }
}

/// Manifest update command.
#[derive(Debug, Args)]
pub struct ManifestUpdateCommand {
    /// Filename for the image to update.
    image: PathBuf,
    /// Filename for an HJSON configuration specifying manifest fields.
    #[arg(short, long)]
    manifest: Option<PathBuf>,
    /// Filename for an HJSON configuration specifying manifest extension fields.
    #[arg(long)]
    manifest_ext: Option<PathBuf>,
    /// Update the length field of the manifest automatically.
    #[arg(long, action = clap::ArgAction::Set, default_value = "true")]
    update_length: bool,
    /// Filename for an external ECDSA signature file.
    #[arg(long)]
    ecdsa_signature: Option<PathBuf>,
    /// Filename for an external RSA signature file.
    #[arg(long)]
    rsa_signature: Option<PathBuf>,
    /// Filename for an external SPHINCS+ signature file.
    #[arg(short, long)]
    spx_signature: Option<PathBuf>,
    /// Filename for the ECDSA key corresponding to the signature.
    ///
    /// Passing a private key indicates the key will be used for signing.
    #[arg(long)]
    ecdsa_key: Option<PathBuf>,
    /// Filename for the RSA PKCS8 key corresponding to the signature.
    ///
    /// Passing a private key indicates the key will be used for signing.
    #[arg(long)]
    rsa_key: Option<PathBuf>,
    /// Filename for the SPHINCS+ key corresponding to the signature.
    ///
    /// Passing a private key indicates the key will be used for signing.
    #[arg(long)]
    spx_key: Option<PathBuf>,
    /// Filename to write the output to instead of updating the input file.
    #[arg(short, long)]
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

fn load_ecdsa_key(key_file: &Path) -> Result<(EcdsaPublicKey, Option<EcdsaPrivateKey>)> {
    match EcdsaPublicKey::load(key_file) {
        Ok(key) => Ok((key, None)),
        Err(_) => match EcdsaPrivateKey::load(key_file) {
            Ok(key) => Ok((key.public_key(), Some(key))),
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
        let mut update_length = self.update_length;

        // Some sanity check
        image
            .manifest_sanity_check()
            .context("Image doesn't appear to contain a manifest, or the manifest is corrupted")?;

        // Load the manifest HJSON definition and update the image.
        if let Some(manifest) = &self.manifest {
            let def = ManifestSpec::read_from_file(manifest)?;
            update_length = !def.has_length();
            image.overwrite_manifest(def)?;
        }

        // Load the manifest extension HJSON definition and update the image.
        let ext = self
            .manifest_ext
            .as_deref()
            .map(ManifestExtSpec::read_from_file)
            .unwrap_or(Ok(Default::default()))?;
        image.add_signed_manifest_extensions(&ext)?;

        // Update the manifest fields that are in the signed region.
        // Load / write RSA public key.
        let mut rsa_private_key: Option<RsaPrivateKey> = None;
        if let Some(key) = &self.rsa_key {
            ensure!(
                self.ecdsa_key.is_none(),
                "Cannot specify both RSA and ECDSA keys"
            );
            let (public, private) = load_rsa_key(key)?;
            image.update_modulus(public.modulus())?;
            if let Some(private) = private {
                rsa_private_key = Some(private);
            }
        }

        // Load / write ECDSA public key.
        let mut ecdsa_private_key: Option<EcdsaPrivateKey> = None;
        if let Some(key) = &self.ecdsa_key {
            ensure!(
                self.rsa_key.is_none(),
                "Cannot specify both RSA and ECDSA keys"
            );
            let (public, private) = load_ecdsa_key(key)?;
            image.update_ecdsa_public_key(EcdsaRawPublicKey::try_from(&public)?)?;
            if let Some(private) = private {
                ecdsa_private_key = Some(private);
            }
        }

        // Load / write SPX+ public key.
        let mut spx_private_key: Option<SpxKeypair> = None;
        if let Some(key) = &self.spx_key {
            let key = spx::load_spx_key(key)?;
            let key_ext = ManifestExtEntry::new_spx_key_entry(&key)?;
            image.add_manifest_extension(key_ext)?;
            if let SpxKey::Private(private) = key {
                spx_private_key = Some(private);
            }
        }
        // Allocate space for `spx_signature` (this impacts the manifest `length` field which is in
        // the signed region of the image). Adding this facilitates offline signing.
        if self.spx_key.is_some() {
            image.allocate_manifest_extension(
                ManifestExtId::spx_signature.into(),
                std::mem::size_of::<ManifestExtSpxSignature>(),
            )?;
        }

        // Update the manifest fields that are in the unsigned region.
        // These extensions will come after `signed_region_end`.
        image.add_unsigned_manifest_extensions(&ext)?;

        // Update manifest `length` field.
        // This is done by default, and will only be skipped if the `length` field is specified in
        // the manifest HJSON, typically during negative tests.
        if update_length {
            image.update_length()?;
        }

        // List out all signed extensions and set the bounds of the signed region.
        let signed_ids = ext
            .signed_region
            .iter()
            .map(|e| e.id())
            .chain(vec![ManifestExtId::spx_key.into()])
            .collect::<HashSet<u32>>();
        image.update_signed_region(&signed_ids)?;

        // Remove any unused extensions in the table that do not reference extension data.
        image.drop_null_extensions()?;

        // Online signing takes place if private keys are provided.
        // Sign with RSA.
        if let Some(key) = rsa_private_key {
            image.update_rsa_signature(key.sign(&image.compute_digest()?)?)?;
        }
        // Sign with ECDSA.
        if let Some(key) = ecdsa_private_key {
            image.update_ecdsa_signature(key.sign(&image.compute_digest()?)?)?;
        }
        // Sign with SPX+.
        if let Some(key) = spx_private_key {
            image.add_manifest_extension(ManifestExtEntry::new_spx_signature_entry(
                &image.map_signed_region(|buf| key.sign(buf))?,
            )?)?;
        }

        // Offline signing takes place if signatures are provided.
        // Attach RSA signature.
        if let Some(rsa_signature) = &self.rsa_signature {
            ensure!(
                self.ecdsa_signature.is_none(),
                "Cannot specify both RSA and ECDSA signatures"
            );
            let signature = RsaSignature::read_from_file(rsa_signature)?;
            image.update_rsa_signature(signature)?;
        }
        // Attach ECDSA signature.
        if let Some(ecdsa_signature) = &self.ecdsa_signature {
            ensure!(
                self.rsa_signature.is_none(),
                "Cannot specify both RSA and ECDSA signatures"
            );
            let signature = EcdsaRawSignature::read_from_file(ecdsa_signature)?;
            image.update_ecdsa_signature(signature)?;
        }
        // Attach SPX+ signature.
        if let Some(spx_signature) = &self.spx_signature {
            let signature = SpxSignature::read_from_file(spx_signature)?;
            image.add_manifest_extension(ManifestExtEntry::new_spx_signature_entry(&signature)?)?;
        }

        image.write_to_file(self.output.as_ref().unwrap_or(&self.image))?;
        Ok(None)
    }
}

/// Manifest verify command.
#[derive(Debug, Args)]
pub struct ManifestVerifyCommand {
    /// Filename for the image to verify.
    image: PathBuf,
    /// Run verification for SPHINCS+.
    #[arg(short, long)]
    spx: bool,
}

impl CommandDispatch for ManifestVerifyCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = image::Image::read_from_file(&self.image)?;

        let digest = Sha256Digest::from_le_bytes(image.compute_digest()?.to_le_bytes())?;

        // Verify signature.
        let sigverify_params = image.get_sigverify_params_from_manifest()?;
        sigverify_params.verify(&digest)?;

        if self.spx {
            // TODO(#18496)
            bail!("SPHINCS+ verification not supported yet, see lowRISC/opentitan#18496.");
        }

        Ok(None)
    }
}

/// Compute digest command.
#[derive(Debug, Args)]
pub struct DigestCommand {
    /// Filename for the image to calculate the digest for.
    image: PathBuf,
    /// Filename for an output bin file.
    #[arg(short, long)]
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
        let digest = image.compute_digest()?;
        if let Some(bin) = &self.bin {
            let mut file = File::create(bin)?;
            file.write_all(&digest.to_le_bytes())?;
        }
        Ok(Some(Box::new(DigestResponse {
            digest: digest.to_be_bytes(),
        })))
    }
}

/// Compute spx-message command.
#[derive(Debug, Args)]
pub struct SpxMessageCommand {
    /// Filename for the image to calculate the digest for.
    image: PathBuf,
    /// Filename for an output bin file.
    #[arg(short, long)]
    output: PathBuf,
}

impl CommandDispatch for SpxMessageCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let image = image::Image::read_from_file(&self.image)?;
        let mut output = File::create(&self.output)?;
        // Note: the closure returns a Result R, and map_signed region
        // returns Result<R>.  Therefore, double `?` to unwrap both.
        image.map_signed_region(|buf| output.write_all(buf))??;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
#[allow(clippy::large_enum_variant)]
/// Manifest manipulation commands.
pub enum ManifestCommand {
    Show(ManifestShowCommand),
    Update(ManifestUpdateCommand),
    Verify(ManifestVerifyCommand),
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// Image manipulation commands.
pub enum Image {
    Assemble(AssembleCommand),
    #[command(subcommand)]
    Manifest(ManifestCommand),
    Digest(DigestCommand),
    SpxMessage(SpxMessageCommand),
}
