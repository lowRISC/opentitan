// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use clap::Args;
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::{StagedProgressBar, TransportWrapper};
use opentitanlib::bootstrap::{Bootstrap, BootstrapOptions, BootstrapProtocol};
use opentitanlib::image::image::ImageAssembler;
use opentitanlib::transport;
use opentitanlib::util::parse_int::ParseInt;

/// Bootstrap the target device.
#[derive(Debug, Args)]
pub struct BootstrapCommand {
    #[command(flatten)]
    bootstrap_options: BootstrapOptions,
    /// The size of the image to assemble (only valid with mutliple FILE arguments).
    #[arg(long, value_parser = usize::from_str, default_value = "1048576")]
    size: usize,
    /// Whether or not the assembled image is mirrored (only valid with mutliple FILE arguments).
    #[arg(long, action = clap::ArgAction::Set, default_value = "true")]
    mirror: bool,
    /// An image to bootstrap or multiple filename@offset specifiers to assemble into a bootstrap image.
    #[arg(value_name = "FILE", required = true, num_args = 1..)]
    filename: Vec<String>,
}

impl BootstrapCommand {
    fn bootstrap_using_direct_emulator_integration(
        &self,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        ensure!(
            !(self.filename.len() > 1 || self.filename[0].contains('@')),
            "The `emulator` protocol does not support image assembly"
        );
        transport.dispatch(&transport::Bootstrap {
            image_path: PathBuf::from(&self.filename[0]),
        })
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
    ) -> Result<Option<Box<dyn Annotate>>> {
        if self.bootstrap_options.protocol == BootstrapProtocol::Emulator {
            return self.bootstrap_using_direct_emulator_integration(transport);
        }

        let payload = self.payload()?;
        let progress = StagedProgressBar::new();
        Bootstrap::update_with_progress(transport, &self.bootstrap_options, &payload, &progress)?;
        Ok(None)
    }
}
