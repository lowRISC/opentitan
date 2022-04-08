// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings)]
#![deny(unused)]
#![deny(unsafe_code)]

use std::convert::TryFrom;
use std::env;
use std::fs;
use std::mem::size_of;
use std::path::PathBuf;
use std::str::FromStr;

use mundane::hash::Sha256;
use mundane::public::rsa::RsaPkcs1v15;
use mundane::public::rsa::B3072;
use mundane::public::DerPrivateKey;
use mundane::public::Signature;

use anyhow::bail;
use anyhow::ensure;
use anyhow::Context;
use anyhow::Result;

use zerocopy::AsBytes;

use rom_ext_image::image::Image;
use rom_ext_image::image::ManifestBuffer;
use rom_ext_image::manifest;
use rom_ext_image::manifest::Manifest;

use object::read::elf::ElfFile32;
use object::read::ObjectSection;
use object::Object;

// Type aliases for convenience.
type ImageSignature =
    mundane::public::rsa::RsaSignature<B3072, RsaPkcs1v15, Sha256>;
type PrivateKey = mundane::public::rsa::RsaPrivKey<B3072>;

#[derive(Copy, Clone)]
enum ImageType {
    RomExt,
    OwnerStage,
}

impl FromStr for ImageType {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "rom_ext" => Ok(ImageType::RomExt),
            "owner" => Ok(ImageType::OwnerStage),
            _ => bail!("Unexpected image type: {}", s),
        }
    }
}

// TODO: Remove this struct when this functionality is integrated into `opentitantool`.
struct Args {
    image_type: ImageType,
    input_image: PathBuf,
    priv_key: PathBuf,
    elf_file: PathBuf,
    output_image: PathBuf,
}

impl Args {
    pub fn new(args: env::ArgsOs) -> Result<Args> {
        let args = args.skip(1).collect::<Vec<_>>();
        match args.as_slice() {
            [image_type, input_image, priv_key, elf_file, output_image] => Ok(Args {
                    image_type: ImageType::from_str(&image_type.to_string_lossy())?,
                    input_image: PathBuf::from(input_image),
                    priv_key: PathBuf::from(priv_key),
                    elf_file: PathBuf::from(elf_file),
                    output_image: PathBuf::from(output_image),
                }),
            args => bail!("Expected exactly 5 positional arguments: \
                          image type, input image, private key, elf file, and output image, \
                          got: {}.", args.len()),
        }
    }
}

// FIXME: Keeping for now, can be removed if not used in opentitantool.
/// Parses an unsigned big-endian hex string into a little-endian byte vector.
fn _parse_hex_str(hex_str: &str) -> Result<Vec<u8>> {
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
    image_type: ImageType,
    key: &PrivateKey,
    elf: &ElfFile32,
) -> Result<()> {
    let manifest_addr = u32::try_from(
        elf.section_by_name(".manifest")
            .context("Could not find the `.manifest` section.")?
            .address(),
    )?;

    let (identifier, allowed_lengths) = match image_type {
        ImageType::RomExt => (
            manifest::MANIFEST_IDENTIFIER_ROM_EXT,
            manifest::MANIFEST_LENGTH_FIELD_ROM_EXT_MIN
                ..=manifest::MANIFEST_LENGTH_FIELD_ROM_EXT_MAX,
        ),
        ImageType::OwnerStage => (
            manifest::MANIFEST_IDENTIFIER_OWNER_STAGE,
            manifest::MANIFEST_LENGTH_FIELD_OWNER_STAGE_MIN
                ..=manifest::MANIFEST_LENGTH_FIELD_OWNER_STAGE_MAX,
        ),
    };

    *image.manifest = Manifest {
        identifier,
        length: u32::try_from(image.bytes().len())?,
        address_translation: 0x739u32, // kHardenedBoolTrue
        code_start: {
            let addr = u32::try_from(
                elf.section_by_name(".vectors")
                    .context("Could not find the `.vectors` section.")?
                    .address(),
            )?;
            addr.checked_sub(manifest_addr).context("Overflow")?
        },
        code_end: {
            // TODO: Consider requiring all binaries signed by this tool to have a .shutdown section.
            let section = elf
                .section_by_name(".shutdown")
                .or(elf.section_by_name(".text"))
                .context(
                    "Could not find the `.shutdown` or `.text` section.",
                )?;
            let addr = u32::try_from(
                section
                    .address()
                    .checked_add(section.size())
                    .context("Overflow")?,
            )?;
            addr.checked_sub(manifest_addr).context("Overflow")?
        },
        entry_point: {
            let addr = u32::try_from(elf.entry())?;
            addr.checked_sub(manifest_addr).context("Overflow")?
        },
        ..Default::default()
    };

    let modulus_be = key.public_modulus_be();
    let dest = image.manifest.modulus.as_bytes_mut().iter_mut();
    let src = modulus_be.iter().rev().copied();
    ensure!(dest.len() == src.len(), "Unexpected modulus length.");
    for (d, s) in Iterator::zip(dest, src) {
        *d = s;
    }

    /// Checks if an address is word (32-bit) aligned.
    fn is_word_aligned(addr: u32) -> bool {
        return addr % 4 == 0;
    }

    ensure!(
        is_word_aligned(image.manifest.code_start),
        "`code_start` is not word aligned."
    );
    ensure!(
        is_word_aligned(image.manifest.code_end),
        "`code_end` is not word aligned."
    );
    ensure!(
        is_word_aligned(image.manifest.entry_point),
        "`entry_point` is not word aligned."
    );
    ensure!(
        (manifest::MANIFEST_SIZE..image.manifest.code_end)
            .contains(&image.manifest.code_start),
        "`code_start` is outside the allowed range."
    );
    ensure!(
        (manifest::MANIFEST_SIZE..=image.manifest.length)
            .contains(&image.manifest.code_end),
        "`code_end` is outside the allowed range."
    );
    ensure!(
        (image.manifest.code_start..image.manifest.code_end)
            .contains(&image.manifest.entry_point),
        "`entry_point` is outside the code region."
    );
    ensure!(
        allowed_lengths.contains(&image.manifest.length),
        "`length` is outside the allowed range."
    );

    Ok(())
}

/// Calculates the signature for the signed portion of an image.
fn calculate_image_signature(
    image: &Image,
    private_key: &PrivateKey,
) -> Result<ImageSignature> {
    ImageSignature::sign(&private_key, &image.signed_bytes())
        .context("Failed to calculate image signature.")
}

/// Updates the signature of an image.
fn update_image_signature(
    image: &mut Image,
    sig: ImageSignature,
) -> Result<()> {
    let dest = image.manifest.signature.as_bytes_mut().iter_mut();
    let src = sig.bytes().iter().rev().copied();
    ensure!(dest.len() == src.len(), "Unexpected signature length.");
    for (d, s) in Iterator::zip(dest, src) {
        *d = s;
    }
    Ok(())
}

fn main() -> Result<()> {
    // TODO(#6915): Convert this to a unit test after we start running rust tests during our
    // builds.
    manifest::check_manifest_layout();
    let args = Args::new(env::args_os())?;

    // We use a separate buffer for manifest because it must have the same alignment as `Manifest`
    // to be able to use `LayoutVerified::new()` and the approach we use to ensure this requires
    // its size to be known at compile time.
    let payload = &fs::read(&args.input_image).with_context(|| {
        format!("Failed to read {}", args.input_image.display())
    })?[size_of::<Manifest>()..];
    let mut manifest_buffer = ManifestBuffer::new();
    let mut image = Image::new(&mut manifest_buffer, payload)?;

    let key = fs::read(&args.priv_key).with_context(|| {
        format!("Failed to read the key from `{}`.", args.priv_key.display())
    })?;
    let key =
        PrivateKey::parse_from_der(&key).context("Failed to parse the key.")?;

    let elf = fs::read(&args.elf_file)?;
    let elf = ElfFile32::parse(elf.as_slice())?;

    update_image_manifest(&mut image, args.image_type, &key, &elf)?;
    let sig = calculate_image_signature(&image, &key)?;
    update_image_signature(&mut image, sig)?;

    fs::write(&args.output_image, image.bytes()).with_context(|| {
        format!(
            "Failed to write the image to {}",
            args.output_image.display()
        )
    })?;
    Ok(())
}
