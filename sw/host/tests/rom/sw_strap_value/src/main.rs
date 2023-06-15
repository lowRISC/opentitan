// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::Result;
use clap::Parser;
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::test_utils::e2e_command::TestCommand;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::test_utils::status::Status;
use opentitanlib::uart::console::UartConsole;
use std::time::Duration;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(
        long,
        value_parser = humantime::parse_duration,
        default_value = "180s",
        help = "Console receive timeout",
    )]
    timeout: Duration,
}

fn sw_strap_set(transport: &TransportWrapper, value: u8) -> Result<()> {
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

fn test_sw_strap_values(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("console")?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    for value in 0..64 {
        log::info!("Setting strap value to {:x}", value);
        sw_strap_set(transport, value)?;
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
