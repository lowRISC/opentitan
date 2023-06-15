// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, ensure, Result};
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::convert::TryInto;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use zerocopy::{AsBytes, LayoutVerified};

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

use opentitanlib::crypto::rsa::{Modulus, RsaPrivateKey, RsaPublicKey, Signature as RsaSignature};
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::crypto::spx::{self, SpxKey, SpxKeypair, SpxPublicKeyPart, SpxSignature};
use opentitanlib::image::image::{self, ImageAssembler};
use opentitanlib::image::manifest::{
    ManifestExtHeader, ManifestExtSpxKey, ManifestExtSpxSignature, SigverifySpxKey,
    MANIFEST_EXT_ID_SPX_KEY, MANIFEST_EXT_ID_SPX_SIGNATURE, MANIFEST_EXT_NAME_SPX_KEY,
    MANIFEST_EXT_NAME_SPX_SIGNATURE,
};
use opentitanlib::image::manifest_def::ManifestSpec;
use opentitanlib::util::file::{FromReader, ToWriter};
use opentitanlib::util::parse_int::ParseInt;

/// Bootstrap the target device.
#[derive(Debug, Args)]
pub struct AssembleCommand {
    #[arg(
        short,
        long,
        value_parser = usize::from_str,
        default_value="1048576",
        help="The size of the image to assemble"
    )]
    size: usize,
    #[arg(
        short,
        long,
        action = clap::ArgAction::Set,
        default_value = "true",
        help = "Whether or not the assembled image is mirrored"
    )]
    mirror: bool,
    #[arg(short, long, help = "Filename to write the assembled image to")]
    output: PathBuf,
    #[arg(
        name = "FILE",
        required = true,
        num_args = 1..,
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
        // The `min_values` arg attribute should take care of this, but it doesn't.
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
#[derive(Debug, Args)]
pub struct ManifestShowCommand {
    #[arg(name = "IMAGE", help = "Filename for the image to display")]
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
#[derive(Debug, Args)]
pub struct ManifestUpdateCommand {
    #[arg(name = "IMAGE", help = "Filename for the image to update")]
    image: PathBuf,
    #[arg(
        short,
        long,
        help = "Filename for an HJSON configuration specifying manifest fields"
    )]
    manifest: Option<PathBuf>,

    #[arg(long, help = "Filename for an external RSA signature file")]
    rsa_signature: Option<PathBuf>,
    #[arg(short, long, help = "Filename for an external SPHINCS+ signature file")]
    spx_signature: Option<PathBuf>,
    #[arg(
        long,
        help = "Filename for the RSA PKCS8 key corresponding to the signature",
        long_help = "Passing a private key indicates the key will be used for signing."
    )]
    rsa_key: Option<PathBuf>,
    #[arg(
        long,
        help = "Filename for the SPHINCS+ key corresponding to the signature",
        long_help = "Passing a private key indicates the key will be used for signing."
    )]
    spx_key: Option<PathBuf>,
    #[arg(
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

        // A u8 buffer with u32 alignment to be able to deserialize bytes for extensions.
        // Note: This should ideally be based on the alignment requirements of the extensions but
        // just using `u32` works since all extensions we have are u32-aligned. We can't miss If
        // this doesn't hold since `LayoutVerified::new()` errors out.
        #[repr(C)]
        pub struct Buffer32 {
            pub bytes: [u8; image::Image::MAX_SIZE],
            _align: [u32; 0],
        }
        let mut buf = Buffer32 {
            bytes: [0; image::Image::MAX_SIZE],
            _align: [],
        };

        // Update `signed_region_end` if it is 0, otherwise it has already been set (i.e., to
        // support offline signing scenarios).
        if image.borrow_manifest()?.signed_region_end == 0 {
            image.update_signed_region_end()?;
        }

        let mut spx_private_key: Option<SpxKeypair> = None;
        if let Some(key) = &self.spx_key {
            let key = spx::load_spx_key(key)?;
            // Add the SPX key extension
            let key_bytes = key.pk_as_bytes();
            buf.bytes[0..key_bytes.len()].copy_from_slice(key_bytes);
            image.set_extension_entry(0, MANIFEST_EXT_ID_SPX_KEY, image.size as u32)?;
            image.add_extension_data(
                ManifestExtSpxKey {
                    header: ManifestExtHeader {
                        identifier: MANIFEST_EXT_ID_SPX_KEY,
                        name: MANIFEST_EXT_NAME_SPX_KEY,
                    },
                    key: *LayoutVerified::<_, SigverifySpxKey>::new(&buf.bytes[0..key_bytes.len()])
                        .unwrap()
                        .into_ref(),
                }
                .as_bytes(),
            )?;
            if let SpxKey::Private(private) = key {
                spx_private_key = Some(private);
            }

            // Update `signed_region_end` after adding all signed extensions (which is just SPX key
            // extension for now).
            image.update_signed_region_end()?;
        }

        if self.spx_key.is_some() {
            image.set_extension_entry(1, MANIFEST_EXT_ID_SPX_SIGNATURE, image.size as u32)?;
            image.add_extension_data(
                ManifestExtSpxSignature {
                    header: ManifestExtHeader {
                        identifier: MANIFEST_EXT_ID_SPX_SIGNATURE,
                        name: MANIFEST_EXT_NAME_SPX_SIGNATURE,
                    },
                    ..Default::default()
                }
                .as_bytes(),
            )?;
        }

        // Update `length` to be able to generate signatures.
        image.update_length()?;

        // Apply the manifest values to the image.
        if let Some(manifest) = &self.manifest {
            let def = ManifestSpec::read_from_file(manifest)?;
            image.overwrite_manifest(def)?;
        }

        // Sign the image
        if let Some(key) = rsa_private_key {
            image.update_rsa_signature(key.sign(&image.compute_digest()?)?)?;
        }

        let spx_signature = if let Some(spx_sig_file) = &self.spx_signature {
            Some(SpxSignature::read_from_file(spx_sig_file)?)
        } else if let Some(key) = spx_private_key {
            Some(image.map_signed_region(|buf| key.sign(buf))?)
        } else {
            None
        };
        if let Some(spx_signature) = spx_signature {
            let sig_bytes = spx_signature.0.to_le_bytes();
            image.update_extension_data(MANIFEST_EXT_ID_SPX_SIGNATURE, &sig_bytes)?;
        }

        if let Some(rsa_signature) = &self.rsa_signature {
            let signature = RsaSignature::read_from_file(rsa_signature)?;
            image.update_rsa_signature(signature)?;
        }

        image.write_to_file(self.output.as_ref().unwrap_or(&self.image))?;
        Ok(None)
    }
}

/// Manifest verify command.
#[derive(Debug, Args)]
pub struct ManifestVerifyCommand {
    #[arg(name = "IMAGE", help = "Filename for the image to verify")]
    image: PathBuf,
    #[arg(short, long, help = "Run verification for SPHINCS+")]
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
        let digest = Sha256Digest::from_le_bytes(image.compute_digest()?.to_le_bytes())?;
        let rsa_key = RsaPublicKey::new(Modulus::from_le_bytes(rsa_modulus.to_le_bytes())?)?;
        let rsa_sig = RsaSignature::from_le_bytes(rsa_sig.to_le_bytes())?;
        rsa_key.verify(&digest, &rsa_sig)?;

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
    #[arg(
        name = "IMAGE",
        help = "Filename for the image to calculate the digest for"
    )]
    image: PathBuf,
    #[arg(short, long, help = "Filename for an output bin file")]
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
    #[arg(
        name = "IMAGE",
        help = "Filename for the image to calculate the digest for"
    )]
    image: PathBuf,
    #[arg(short, long, help = "Filename for an output bin file")]
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
