// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use anyhow::{ensure, Result};

use opentitanlib::app::TransportWrapper;
use opentitanlib::io::gpio::{PinMode, PullMode};

pub struct Config {
    // List of the output IO names of the transport.
    pub output_pins: Vec<&'static str>,
    // If true, the input pin will be setup in open drain mode (with a pullup), otherwise
    // in push-pull mode. The order must match the one in pins.
    pub open_drain: Vec<bool>,
    // List of the input IO names of the transport.
    pub input_pins: Vec<&'static str>,
}

/// Configure earlgrey and debugger pins.
pub fn setup_pins(transport: &TransportWrapper, config: &Config) -> Result<()> {
    log::info!("Configuring transport GPIOs");
    // Since the EC reset and flash WP pins are open drain, configure those hyperdebug pins as
    // open drain with pullup.
    assert_eq!(config.output_pins.len(), config.open_drain.len());
    for (pin,od) in std::iter::zip(&config.output_pins, &config.open_drain) {
        log::info!("output pin {}: {}", pin, od);
        if *od {
            transport.gpio_pin(pin)?.set_mode(PinMode::OpenDrain)?;
            transport.gpio_pin(pin)?.set_pull_mode(PullMode::PullUp)?;
        }
        else {
            transport.gpio_pin(pin)?.set_mode(PinMode::PushPull)?;
        }
    }
    for pin in &config.input_pins {
        log::info!("input pin {}", pin);
        transport.gpio_pin(pin)?.set_mode(PinMode::Input)?;
    }
    Ok(())
}

/// Set pins: the i-th bit of `values` corresponds to the i-th entry of `config.output_pins`.
pub fn set_pins(transport: &TransportWrapper, config: &Config, values: u8) -> Result<()> {
    log::info!("Set pins to {:b}", values);
    // Set pins on the transport.
    for (i, pin) in config.output_pins.iter().enumerate() {
        transport
            .gpio_pin(pin)?
            .write(((values >> i) & 0b1) == 0b1)?;
    }
    Ok(())
}
