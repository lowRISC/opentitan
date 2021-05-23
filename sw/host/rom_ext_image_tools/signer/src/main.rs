// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings)]
#![deny(unused)]
#![deny(unsafe_code)]

use std::env;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::convert::TryFrom;

use rom_ext_image::image::Image;
use rom_ext_image::manifest;

use mundane::hash::Sha256;
use mundane::public::rsa::RsaPkcs1v15;
use mundane::public::rsa::B3072;
use mundane::public::DerPrivateKey;
use mundane::public::Signature;

use anyhow::bail;
use anyhow::ensure;
use anyhow::Context;
use anyhow::Result;

// Type aliases for convenience.
type ImageSignature =
    mundane::public::rsa::RsaSignature<B3072, RsaPkcs1v15, Sha256>;
type PrivateKey = mundane::public::rsa::RsaPrivKey<B3072>;

// TODO: Remove this struct when this functionality is integrated into `opentitantool`.
struct Args {
    input: PathBuf,
    priv_key: PathBuf,
    output: PathBuf,
}

impl Args {
    pub fn new(args: env::ArgsOs) -> Result<Args> {
        let args = args.skip(1).collect::<Vec<_>>();
        match args.as_slice() {
            [input, priv_key, output] => Ok(Args {
                    input: PathBuf::from(input),
                    priv_key: PathBuf::from(priv_key),
                    output: PathBuf::from(output),
                }),
            args => bail!("Expected exactly 3 positional arguments: input, private key, and output, got: {}.", args.len()),
        }
    }
}

/// Parses an unsigned big-endian hex string into a little-endian byte vector.
fn parse_hex_str(hex_str: &str) -> Result<Vec<u8>> {
    ensure!(
        hex_str.starts_with("0x")
            && hex_str.len() > 2
            && hex_str.len() % 2 == 0,
        "Invalid hex string: {}",
        hex_str
    );
    let bytes = (2..hex_str.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex_str[i..i + 2], 16))
        .rev()
        .collect::<Result<_, _>>()?;
    Ok(bytes)
}

/// Updates the manifest of an image.
// TODO: This function must use a public key.
fn update_image_manifest(
    image: &mut Image,
    key: impl AsRef<Path>,
) -> Result<()> {
    let key = fs::read(&key).with_context(|| {
        format!("Failed to read the key from `{}`.", key.as_ref().display())
    })?;
    let key =
        PrivateKey::parse_from_der(&key).context("Failed to parse the key.")?;

    image.set_manifest_field(
        &manifest::ROM_EXT_SIGNATURE_KEY_PUBLIC_EXPONENT,
        key.public_exponent_be().iter().rev().cloned(),
    )?;
    image.set_manifest_field(
        &manifest::ROM_EXT_SIGNATURE_KEY_MODULUS,
        key.public_modulus_be().iter().rev().cloned(),
    )?;
    image.set_manifest_field(
        &manifest::ROM_EXT_MANIFEST_IDENTIFIER,
        parse_hex_str("0x4552544f")?,
    )?;

    image.set_manifest_field(
        &manifest::ROM_EXT_IMAGE_VERSION,
        // TODO: Use into_iter once it's stabilized (for all usages in this file).
        std::array::IntoIter::new(0_u32.to_le_bytes()),
    )?;

    // TODO: Do we need these fields?
    let extensions = [
        (
            &manifest::ROM_EXT_EXTENSION0_OFFSET,
            &manifest::ROM_EXT_EXTENSION0_CHECKSUM,
        ),
        (
            &manifest::ROM_EXT_EXTENSION1_OFFSET,
            &manifest::ROM_EXT_EXTENSION1_CHECKSUM,
        ),
        (
            &manifest::ROM_EXT_EXTENSION2_OFFSET,
            &manifest::ROM_EXT_EXTENSION2_CHECKSUM,
        ),
        (
            &manifest::ROM_EXT_EXTENSION3_OFFSET,
            &manifest::ROM_EXT_EXTENSION3_CHECKSUM,
        ),
    ];
    for fields in &extensions {
        image.set_manifest_field(
            fields.0,
            std::array::IntoIter::new(0_u32.to_le_bytes()),
        )?;
        image.set_manifest_field(
            fields.1,
            std::array::IntoIter::new(0_u32.to_le_bytes()),
        )?;
    }
    image.set_manifest_field(
        &manifest::ROM_EXT_USAGE_CONSTRAINTS,
        std::array::IntoIter::new(
            [0; manifest::ROM_EXT_USAGE_CONSTRAINTS.size_bytes],
        ),
    )?;
    image.set_manifest_field(
        &manifest::ROM_EXT_PERIPHERAL_LOCKDOWN_INFO,
        std::array::IntoIter::new(
            [0; manifest::ROM_EXT_PERIPHERAL_LOCKDOWN_INFO.size_bytes],
        ),
    )?;
    image.set_manifest_field(
        &manifest::ROM_EXT_IMAGE_TIMESTAMP,
        std::array::IntoIter::new(0_u64.to_le_bytes()),
    )?;
    image.set_manifest_field(
        &manifest::ROM_EXT_IMAGE_LENGTH,
        std::array::IntoIter::new(u32::try_from(image.len())?.to_le_bytes()),
    )?;

    Ok(())
}

/// Calculates the signature for the signed portion of an image.
fn calculate_image_signature(
    image: &Image,
    key: impl AsRef<Path>,
) -> Result<ImageSignature> {
    let key = fs::read(&key).with_context(|| {
        format!("Failed to read key from `{}`.", key.as_ref().display())
    })?;
    let key =
        PrivateKey::parse_from_der(&key).context("Failed to parse the key.")?;
    let sig = ImageSignature::sign(&key, image.signed_bytes())
        .context("Failed to sign the image.")?;
    Ok(sig)
}

/// Updates the signature of an image.
fn update_image_signature(
    image: &mut Image,
    signature: ImageSignature,
) -> Result<()> {
    image.set_manifest_field(
        &manifest::ROM_EXT_IMAGE_SIGNATURE,
        signature.bytes().iter().rev().cloned(),
    )?;
    Ok(())
}

fn main() -> Result<()> {
    let args = Args::new(env::args_os())?;
    let mut image = Image::from(fs::read(&args.input).with_context(|| {
        format!("Failed to read the image from {}", args.input.display())
    })?);

    // TODO for a future refactor into opentitantool: These functions probably should belong to a
    // Signer struct and should move into the image crate.
    // TODO: This must use the public key.
    update_image_manifest(&mut image, &args.priv_key)?;
    let sig = calculate_image_signature(&image, &args.priv_key)?;
    update_image_signature(&mut image, sig)?;
    fs::write(&args.output, image).with_context(|| {
        format!("Failed to write the image to {}", args.output.display())
    })?;
    Ok(())
}
