// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;
use structopt::clap::arg_enum;
use thiserror::Error;

use crate::io::gpio::GpioPin;
use crate::io::spi::Target;

mod legacy;
mod primitive;

#[derive(Debug, Error)]
pub enum BootstrapError {
    #[error("Invalid hash length: {0}")]
    InvalidHashLength(usize),
}

arg_enum! {
    /// `BootstrapProtocol` describes the supported types of bootstrap.
    /// The `Primitive` protocol is used by OpenTitan during development.
    /// The `Legacy` protocol is used by previous generations of Google Titan-class chips.
    /// The `Eeprom` protocol is planned to be implemented for OpenTitan.
    /// The 'Emulator' value indicates that this tool has a direct way
    /// of communicating with the OpenTitan emulator, to replace the
    /// contents of the emulated flash storage.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum BootstrapProtocol {
        Primitive,
        Legacy,
        Eeprom,
        Emulator,
    }
}

// Implementations of bootstrap need to implement the `UpdateProtocol` trait.
trait UpdateProtocol {
    fn update(&self, spi: &dyn Target, payload: &[u8]) -> Result<()>;
}

/// Options which control bootstrap behavior.
/// The meaning of each of these values depends on the specific bootstrap protocol being used.
#[derive(Debug, Default)]
pub struct BootstrapOptions {
    /// How long to hold the reset pin during the reset sequence.
    pub reset_delay: Option<Duration>,
    /// How long to delay between sending bootstrap frames.
    pub inter_frame_delay: Option<Duration>,
    /// How long to delay during a flash erase operation.
    pub flash_erase_delay: Option<Duration>,
}

/// Bootstrap wraps and drives the various bootstrap protocols.
pub struct Bootstrap {
    pub protocol: BootstrapProtocol,
    reset_delay: Duration,
    updater: Box<dyn UpdateProtocol>,
}

impl Bootstrap {
    const RESET_DELAY: Duration = Duration::from_millis(200);

    /// Consrtuct a `Bootstrap` struct configured to use `protocol` and `options`.
    pub fn new(protocol: BootstrapProtocol, options: BootstrapOptions) -> Result<Self> {
        let updater: Box<dyn UpdateProtocol> = match protocol {
            BootstrapProtocol::Primitive => Box::new(primitive::Primitive::new(&options)),
            BootstrapProtocol::Legacy => Box::new(legacy::Legacy::new(&options)),
            BootstrapProtocol::Eeprom => {
                unimplemented!();
            }
            BootstrapProtocol::Emulator => {
                // Not intended to be implemented by this struct.
                unimplemented!();
            }
        };
        Ok(Bootstrap {
            protocol,
            reset_delay: options.reset_delay.unwrap_or(Self::RESET_DELAY),
            updater: updater,
        })
    }

    /// Perform the update, sending the firmware `payload` to the `spi` target,
    /// using `gpio` to sequence the reset and bootstrap pins.
    pub fn update(
        &self,
        spi: &dyn Target,
        reset: &dyn GpioPin,
        bootstrap: &dyn GpioPin,
        payload: &[u8],
    ) -> Result<()> {
        log::info!("Asserting bootstrap pins...");
        bootstrap.write(true)?;

        log::info!("Restting the target...");
        reset.write(false)?; // Low active
        std::thread::sleep(self.reset_delay);
        reset.write(true)?; // Release reset
        std::thread::sleep(self.reset_delay);

        log::info!("Performing bootstrap...");
        self.updater.update(spi, payload)?;

        log::info!("Releasing bootstrap pins...");
        bootstrap.write(false)?;
        Ok(())
    }
}
