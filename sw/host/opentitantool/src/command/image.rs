// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use erased_serde::Serialize;
use std::any::Any;
use std::convert::TryInto;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

use opentitanlib::image::image::{self, ImageAssembler};
use opentitanlib::image::manifest_def::ManifestDef;
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
    ) -> Result<Option<Box<dyn Serialize>>> {
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
    ) -> Result<Option<Box<dyn Serialize>>> {
        let image = image::Image::read_from_file(&self.image)?;
        let manifest_def: ManifestDef = image.borrow_manifest()?.try_into()?;
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
    hjson_file: Option<PathBuf>,
    #[structopt(short, long, help = "Filename for a signature file")]
    signature_file: Option<PathBuf>,
    #[structopt(
        short,
        long,
        help = "Filename to write the output to instead of updating the input file"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for ManifestUpdateCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        let mut image = image::Image::read_from_file(&self.image)?;

        self.hjson_file.as_ref().map(|hjson| -> Result<()> {
            let def = ManifestDef::read_from_file(&hjson)?;
            image.overwrite_manifest(def)
        });

        // TODO: Add signature update.

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
    ) -> Result<Option<Box<dyn Serialize>>> {
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
    ) -> Result<Option<Box<dyn Serialize>>> {
        let image = image::Image::read_from_file(&self.image)?;
        let digest = image.compute_digest();
        if let Some(bin) = &self.bin {
            let mut file = File::create(bin)?;
            file.write(&digest)?;
        }
        Ok(Some(Box::new(DigestResponse {
            digest: format!("{}", hex::encode(&digest)),
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
