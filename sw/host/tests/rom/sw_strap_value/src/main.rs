// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{anyhow, Result};
use clap::Parser;
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::test_utils::e2e_command::TestCommand;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::test_utils::status::Status;
use opentitanlib::uart::console::UartConsole;
use std::time::Duration;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "180s")]
    timeout: Duration,
}

fn sw_strap_set_teacup(transport: &TransportWrapper, value: u8) -> Result<()> {
    // The teacup board has some hyperdebug GPIOs dedicated to driving the
    // weak values.
    let pin_pairs = [
        (
            transport.gpio_pin("SW_STRAP0")?,
            transport.gpio_pin("SW_STRAP0_WEAK")?,
        ),
        (
            transport.gpio_pin("SW_STRAP1")?,
            transport.gpio_pin("SW_STRAP1_WEAK")?,
        ),
        (
            transport.gpio_pin("SW_STRAP2")?,
            transport.gpio_pin("SW_STRAP2_WEAK")?,
        ),
    ];
    for (i, (strong, weak)) in pin_pairs.iter().enumerate() {
        let pinval = ((value >> (2 * i)) & 3) as usize;
        if pinval == 0 || pinval == 3 {
            // For the strong strap values, we set the strong pin to PushPull
            // and drive the value.  We set the weak pin to Input to tri-state.
            strong.set(Some(PinMode::PushPull), Some(pinval == 3), None, None)?;
            weak.set(Some(PinMode::Input), None, None, None)?;
        } else {
            // For the weak strap values, we set the weak pin to PushPull and
            // drive the value.  We set the strong pin to Input to tri-state.
            weak.set(Some(PinMode::PushPull), Some(pinval == 2), None, None)?;
            strong.set(Some(PinMode::Input), None, None, None)?;
        }
    }
    Ok(())
}

fn sw_strap_set_verilator(transport: &TransportWrapper, value: u8) -> Result<()> {
    let dont_care = false;
    let settings = [
        (PinMode::PushPull, false, PullMode::None),
        (PinMode::Input, dont_care, PullMode::PullDown),
        (PinMode::Input, dont_care, PullMode::PullUp),
        (PinMode::PushPull, true, PullMode::None),
    ];
    let pins = [
        transport.gpio_pin("IOC0")?,
        transport.gpio_pin("IOC1")?,
        transport.gpio_pin("IOC2")?,
    ];
    for (i, pin) in pins.iter().enumerate() {
        let pinval = ((value >> (2 * i)) & 3) as usize;
        pin.set(
            Some(settings[pinval].0),
            Some(settings[pinval].1),
            Some(settings[pinval].2),
            None,
        )?;
    }
    Ok(())
}

fn strap_pattern(value: u8) -> String {
    let bits = [
        b's', // Strong zero.
        b'w', // Weak zero.
        b'W', // Weak one.
        b'S', // Strong one.
    ];
    let mut buf = [b'X'; 3];
    for i in 0..3 {
        let v = (value >> (2 * i)) & 3;
        buf[2 - i] = bits[v as usize];
    }
    return std::str::from_utf8(&buf).unwrap().into();
}

fn test_sw_strap_values(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("console")?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    for value in 0..64 {
        log::info!(
            "Setting strap value to {value:02x}, pattern = {}",
            strap_pattern(value)
        );
        match opts.init.backend_opts.interface.as_str() {
            "teacup" => sw_strap_set_teacup(transport, value)?,
            "verilator" => sw_strap_set_verilator(transport, value)?,
            intf => return Err(anyhow!("Unsupported interface: {intf}")),
        };
        if opts.init.backend_opts.interface == "teacup" {
            sw_strap_set_teacup(transport, value)?;
        } else {
            sw_strap_set_verilator(transport, value)?;
        }
        TestCommand::SwStrapRead.send(&*uart)?;
        let response = Status::recv(&*uart, opts.timeout, false)?;
        assert_eq!(value, u8::try_from(response)?);
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_sw_strap_values, &opts, &transport);
    Ok(())
}
