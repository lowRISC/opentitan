// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use erased_serde::Serialize;
use humantime::parse_duration;
use std::any::Any;
use std::path::PathBuf;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::bootstrap::{Bootstrap, BootstrapOptions, BootstrapProtocol};
use opentitanlib::io::spi::SpiParams;
use opentitanlib::transport;
use opentitanlib::transport::Capability;
use opentitanlib::util::image::ImageAssembler;
use opentitanlib::util::parse_int::ParseInt;

/// Bootstrap the target device.
#[derive(Debug, StructOpt)]
pub struct BootstrapCommand {
    #[structopt(flatten)]
    params: SpiParams,
    #[structopt(
        short,
        long,
        possible_values = &BootstrapProtocol::variants(),
        case_insensitive = true,
        default_value = "primitive",
        help = "Bootstrap protocol to use"
    )]
    protocol: BootstrapProtocol,
    #[structopt(long, parse(try_from_str=parse_duration), help = "Duration of the reset delay")]
    reset_delay: Option<Duration>,
    #[structopt(long, parse(try_from_str=parse_duration), help = "Duration of the inter-frame delay")]
    inter_frame_delay: Option<Duration>,
    #[structopt(long, parse(try_from_str=parse_duration), help = "Duration of the flash-erase delay")]
    flash_erase_delay: Option<Duration>,
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
    ) -> Result<Option<Box<dyn Serialize>>> {
        // The `min_values` structopt attribute should take care of this, but it doesn't.
        ensure!(
            !self.filename.is_empty(),
            "You must supply at least one filename"
        );
        if self.protocol == BootstrapProtocol::Emulator {
            return self.bootstrap_using_direct_emulator_integration(transport);
        }

        transport
            .capabilities()
            .request(Capability::GPIO | Capability::SPI)
            .ok()?;

        let options = BootstrapOptions {
            reset_delay: self.reset_delay,
            inter_frame_delay: self.inter_frame_delay,
            flash_erase_delay: self.flash_erase_delay,
        };
        let bootstrap = Bootstrap::new(self.protocol, options)?;

        let spi = self.params.create(transport)?;
        let reset_pin = transport.gpio_pin("RESET")?;
        let bootstrap_pin = transport.gpio_pin("BOOTSTRAP")?;
        let payload = self.payload()?;
        bootstrap.update(&*spi, &*reset_pin, &*bootstrap_pin, &payload)?;
        Ok(None)
    }
}
