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
use opentitanlib::app::TransportWrapper;
use opentitanlib::bootstrap::{Bootstrap, BootstrapOptions, BootstrapProtocol};
use opentitanlib::io::spi::SpiParams;
use opentitanlib::transport::Capability;
use opentitanlib::transport;

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
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
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
        let payload = std::fs::read(&self.filename)?;
        bootstrap.update(&*spi, &*reset_pin, &*bootstrap_pin, &payload)?;
        Ok(None)
    }
}

impl BootstrapCommand {
    fn bootstrap_using_direct_emulator_integration(
        &self,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.dispatch(&mut transport::Bootstrap {
            image_path: self.filename.clone()
        })
    }
}
