// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use erased_serde::Serialize;
use std::any::Any;
use std::path::PathBuf;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

use opentitanlib::image::image::ImageAssembler;
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

#[derive(Debug, StructOpt, CommandDispatch)]
/// Image manipulation commands.
pub enum Image {
    Assemble(AssembleCommand),
}
