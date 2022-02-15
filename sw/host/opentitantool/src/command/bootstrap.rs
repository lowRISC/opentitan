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
use opentitanlib::bootstrap::{Bootstrap, BootstrapOptions, BootstrapProtocol};
use opentitanlib::transport;
use opentitanlib::util::image::ImageAssembler;
use opentitanlib::util::parse_int::ParseInt;

/// Bootstrap the target device.
#[derive(Debug, StructOpt)]
pub struct BootstrapCommand {
    #[structopt(flatten)]
    bootstrap_options: BootstrapOptions,
    #[structopt(
        long,
        parse(try_from_str=usize::from_str),
        default_value="1048576",
        help="The size of the image to assemble (only valid with mutliple FILE arguments)"
    )]
    size: usize,
    #[structopt(
        long,
        parse(try_from_str),
        default_value = "true",
        help = "Whether or not the assembled image is mirrored (only valid with mutliple FILE arguments)"
    )]
    mirror: bool,
    #[structopt(
        name = "FILE",
        min_values(1),
        help = "An image to bootstrap or multiple filename@offset specifiers to assemble into a bootstrap image."
    )]
    filename: Vec<String>,
}

impl BootstrapCommand {
    fn bootstrap_using_direct_emulator_integration(
        &self,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        ensure!(
            !(self.filename.len() > 1 || self.filename[0].contains('@')),
            "The `emulator` protocol does not support image assembly"
        );
        Ok(transport.dispatch(&transport::Bootstrap {
            image_path: PathBuf::from(&self.filename[0]),
        })?)
    }

    fn payload(&self) -> Result<Vec<u8>> {
        if self.filename.len() > 1 || self.filename[0].contains('@') {
            let mut image = ImageAssembler::with_params(self.size, self.mirror);
            image.parse(&self.filename)?;
            image.assemble()
        } else {
            Ok(std::fs::read(&self.filename[0])?)
        }
    }
}

impl CommandDispatch for BootstrapCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        // The `min_values` structopt attribute should take care of this, but it doesn't.
        ensure!(
            !self.filename.is_empty(),
            "You must supply at least one filename"
        );
        if self.bootstrap_options.protocol == BootstrapProtocol::Emulator {
            return self.bootstrap_using_direct_emulator_integration(transport);
        }

        Bootstrap::update(&transport, &self.bootstrap_options, &self.payload()?)?;
        Ok(None)
    }
}
