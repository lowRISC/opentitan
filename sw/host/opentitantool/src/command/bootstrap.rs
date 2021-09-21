// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use humantime::parse_duration;
use std::any::Any;
use std::path::PathBuf;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::bootstrap::{Bootstrap, BootstrapOptions, BootstrapProtocol};
use opentitanlib::io::spi::SpiParams;
use opentitanlib::transport::{Capability, Transport};

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
    #[structopt(name = "FILE")]
    filename: PathBuf,
}

impl CommandDispatch for BootstrapCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &mut dyn Transport,
    ) -> Result<Option<Box<dyn Serialize>>> {
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
        let gpio = transport.gpio()?;
        let payload = std::fs::read(&self.filename)?;
        bootstrap.update(&*spi, &*gpio, &payload)?;
        Ok(None)
    }
}
