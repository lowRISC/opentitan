// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use humantime::parse_duration;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use std::time::Duration;
use structopt::clap::arg_enum;
use structopt::StructOpt;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::impl_serializable_error;
use crate::io::gpio::GpioPin;
use crate::io::spi::SpiParams;
use crate::io::uart::UartParams;
use crate::transport::Capability;

mod eeprom;
mod legacy;
mod primitive;
mod rescue;

pub use legacy::LegacyBootstrapError;
pub use rescue::RescueError;

#[derive(Debug, Error, Serialize, Deserialize)]
pub enum BootstrapError {
    #[error("Invalid hash length: {0}")]
    InvalidHashLength(usize),
}
impl_serializable_error!(BootstrapError);

arg_enum! {
    /// `BootstrapProtocol` describes the supported types of bootstrap.
    /// The `Primitive` SPI protocol is used by OpenTitan during development.
    /// The `Legacy` SPI protocol is used by previous generations of Google Titan-class chips.
    /// The `Eeprom` SPI protocol is planned to be implemented for OpenTitan.
    /// The `Rescue` UART protocol is used by Google Ti50 firmware.
    /// The 'Emulator' value indicates that this tool has a direct way
    /// of communicating with the OpenTitan emulator, to replace the
    /// contents of the emulated flash storage.
    #[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
    pub enum BootstrapProtocol {
        Primitive,
        Legacy,
        Eeprom,
        Rescue,
        Emulator,
    }
}

// Implementations of bootstrap need to implement the `UpdateProtocol` trait.
trait UpdateProtocol {
    /// Called before any action is taken, to allow the protocol to verify that the transport
    /// supports SPI/UART or whatever it needs.
    fn verify_capabilities(
        &self,
        container: &Bootstrap,
        transport: &TransportWrapper,
    ) -> Result<()>;
    /// Indicates whether the caller should assert the bootstrap pin and reset the chip, before
    /// invoking update().
    fn uses_common_bootstrap_reset(&self) -> bool;
    /// Invoked to perform the actual transfer of an executable image to the OpenTitan chip.
    fn update(
        &self,
        container: &Bootstrap,
        transport: &TransportWrapper,
        payload: &[u8],
        progress: &dyn Fn(u32, u32),
    ) -> Result<()>;
}

/// Options which control bootstrap behavior.
/// The meaning of each of these values depends on the specific bootstrap protocol being used.
#[derive(Clone, Debug, StructOpt, Serialize, Deserialize)]
pub struct BootstrapOptions {
    #[structopt(flatten)]
    pub uart_params: UartParams,
    #[structopt(flatten)]
    pub spi_params: SpiParams,
    #[structopt(
        short,
        long,
        possible_values = &BootstrapProtocol::variants(),
        case_insensitive = true,
        default_value = "eeprom",
        help = "Bootstrap protocol to use"
    )]
    pub protocol: BootstrapProtocol,
    #[structopt(
        long,
        help = "Whether to reset target and clear UART RX buffer after bootstrap. For CW310 only."
    )]
    pub clear_uart: Option<bool>,
    #[structopt(long, parse(try_from_str=parse_duration), default_value = "100ms", help = "Duration of the reset delay")]
    pub reset_delay: Duration,
    #[structopt(long, parse(try_from_str=parse_duration), help = "Duration of the inter-frame delay")]
    pub inter_frame_delay: Option<Duration>,
    #[structopt(long, parse(try_from_str=parse_duration), help = "Duration of the flash-erase delay")]
    pub flash_erase_delay: Option<Duration>,
}

/// Bootstrap wraps and drives the various bootstrap protocols.
pub struct Bootstrap<'a> {
    pub protocol: BootstrapProtocol,
    pub clear_uart_rx: bool,
    pub uart_params: &'a UartParams,
    pub spi_params: &'a SpiParams,
    reset_pin: Rc<dyn GpioPin>,
    reset_delay: Duration,
}

impl<'a> Bootstrap<'a> {
    /// Perform the update, sending the firmware `payload` to a SPI or UART target depending on
    /// given `options`, which specifies protocol and port to use.
    pub fn update(
        transport: &TransportWrapper,
        options: &BootstrapOptions,
        payload: &[u8],
    ) -> Result<()> {
        Self::update_with_progress(transport, options, payload, |_, _| {})
    }

    /// Perform the update, sending the firmware `payload` to a SPI or UART target depending on
    /// given `options`, which specifies protocol and port to use.  The `progress` callback will
    /// be called with the flash address and length of each chunk sent to the target device.
    pub fn update_with_progress(
        transport: &TransportWrapper,
        options: &BootstrapOptions,
        payload: &[u8],
        progress: impl Fn(u32, u32),
    ) -> Result<()> {
        if transport
            .capabilities()?
            .request(Capability::PROXY)
            .ok()
            .is_ok()
        {
            // The transport happens to be connection to a remove opentitan session.  Pass
            // payload along with all relevant command line arguments to the remote session, and
            // it will run the actual bootstrapping logic.
            transport.proxy_ops()?.bootstrap(options, payload)?;
            return Ok(());
        }
        let updater: Box<dyn UpdateProtocol> = match options.protocol {
            BootstrapProtocol::Primitive => Box::new(primitive::Primitive::new(options)),
            BootstrapProtocol::Legacy => Box::new(legacy::Legacy::new(options)),
            BootstrapProtocol::Rescue => Box::new(rescue::Rescue::new(options)),
            BootstrapProtocol::Eeprom => Box::new(eeprom::Eeprom::new()),
            BootstrapProtocol::Emulator => {
                // Not intended to be implemented by this struct.
                unimplemented!();
            }
        };
        Bootstrap {
            protocol: options.protocol,
            clear_uart_rx: options.clear_uart.unwrap_or(false),
            uart_params: &options.uart_params,
            spi_params: &options.spi_params,
            reset_pin: transport.gpio_pin("RESET")?,
            reset_delay: options.reset_delay,
        }
        .do_update(updater, transport, payload, &progress)
    }

    fn do_update(
        &self,
        updater: Box<dyn UpdateProtocol>,
        transport: &TransportWrapper,
        payload: &[u8],
        progress: &dyn Fn(u32, u32),
    ) -> Result<()> {
        updater.verify_capabilities(self, transport)?;
        let perform_bootstrap_reset = updater.uses_common_bootstrap_reset();

        if perform_bootstrap_reset {
            log::info!("Asserting bootstrap pins...");
            transport.apply_pin_strapping("ROM_BOOTSTRAP")?;
            transport.reset_target(self.reset_delay, self.clear_uart_rx)?;
            log::info!("Performing bootstrap...");
        }
        let result = updater.update(self, transport, payload, progress);

        if perform_bootstrap_reset {
            log::info!("Releasing bootstrap pins...");
            transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
        }

        // Don't clear the UART RX buffer after bootstrap to preserve the bootstrap output.
        transport.reset_target(self.reset_delay, false)?;
        result
    }
}
