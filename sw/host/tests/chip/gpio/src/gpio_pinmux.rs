// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::iter;
use std::str::FromStr;
use std::time::Duration;

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::gpio::{GpioGet, GpioSet};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::pinmux_config::PinmuxConfig;
use opentitanlib::uart::console::UartConsole;
use ot_hal::dif::pinmux::PinmuxPadAttr;
use ot_hal::top::earlgrey::{PinmuxInsel, PinmuxMioOut, PinmuxOutsel, PinmuxPeripheralIn};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

struct Config {
    input: HashMap<PinmuxPeripheralIn, PinmuxInsel>,
    output: HashMap<PinmuxMioOut, PinmuxOutsel>,
}

static GPIOS: [(PinmuxPeripheralIn, PinmuxOutsel); 32] = [
    (PinmuxPeripheralIn::Gpio0Gpio0, PinmuxOutsel::Gpio0Gpio0),
    (PinmuxPeripheralIn::Gpio0Gpio1, PinmuxOutsel::Gpio0Gpio1),
    (PinmuxPeripheralIn::Gpio0Gpio2, PinmuxOutsel::Gpio0Gpio2),
    (PinmuxPeripheralIn::Gpio0Gpio3, PinmuxOutsel::Gpio0Gpio3),
    (PinmuxPeripheralIn::Gpio0Gpio4, PinmuxOutsel::Gpio0Gpio4),
    (PinmuxPeripheralIn::Gpio0Gpio5, PinmuxOutsel::Gpio0Gpio5),
    (PinmuxPeripheralIn::Gpio0Gpio6, PinmuxOutsel::Gpio0Gpio6),
    (PinmuxPeripheralIn::Gpio0Gpio7, PinmuxOutsel::Gpio0Gpio7),
    (PinmuxPeripheralIn::Gpio0Gpio8, PinmuxOutsel::Gpio0Gpio8),
    (PinmuxPeripheralIn::Gpio0Gpio9, PinmuxOutsel::Gpio0Gpio9),
    (PinmuxPeripheralIn::Gpio0Gpio10, PinmuxOutsel::Gpio0Gpio10),
    (PinmuxPeripheralIn::Gpio0Gpio11, PinmuxOutsel::Gpio0Gpio11),
    (PinmuxPeripheralIn::Gpio0Gpio12, PinmuxOutsel::Gpio0Gpio12),
    (PinmuxPeripheralIn::Gpio0Gpio13, PinmuxOutsel::Gpio0Gpio13),
    (PinmuxPeripheralIn::Gpio0Gpio14, PinmuxOutsel::Gpio0Gpio14),
    (PinmuxPeripheralIn::Gpio0Gpio15, PinmuxOutsel::Gpio0Gpio15),
    (PinmuxPeripheralIn::Gpio0Gpio16, PinmuxOutsel::Gpio0Gpio16),
    (PinmuxPeripheralIn::Gpio0Gpio17, PinmuxOutsel::Gpio0Gpio17),
    (PinmuxPeripheralIn::Gpio0Gpio18, PinmuxOutsel::Gpio0Gpio18),
    (PinmuxPeripheralIn::Gpio0Gpio19, PinmuxOutsel::Gpio0Gpio19),
    (PinmuxPeripheralIn::Gpio0Gpio20, PinmuxOutsel::Gpio0Gpio20),
    (PinmuxPeripheralIn::Gpio0Gpio21, PinmuxOutsel::Gpio0Gpio21),
    (PinmuxPeripheralIn::Gpio0Gpio22, PinmuxOutsel::Gpio0Gpio22),
    (PinmuxPeripheralIn::Gpio0Gpio23, PinmuxOutsel::Gpio0Gpio23),
    (PinmuxPeripheralIn::Gpio0Gpio24, PinmuxOutsel::Gpio0Gpio24),
    (PinmuxPeripheralIn::Gpio0Gpio25, PinmuxOutsel::Gpio0Gpio25),
    (PinmuxPeripheralIn::Gpio0Gpio26, PinmuxOutsel::Gpio0Gpio26),
    (PinmuxPeripheralIn::Gpio0Gpio27, PinmuxOutsel::Gpio0Gpio27),
    (PinmuxPeripheralIn::Gpio0Gpio28, PinmuxOutsel::Gpio0Gpio28),
    (PinmuxPeripheralIn::Gpio0Gpio29, PinmuxOutsel::Gpio0Gpio29),
    (PinmuxPeripheralIn::Gpio0Gpio30, PinmuxOutsel::Gpio0Gpio30),
    (PinmuxPeripheralIn::Gpio0Gpio31, PinmuxOutsel::Gpio0Gpio31),
];

static SUPPORTS_OD: [PinmuxMioOut; 14] = [
    PinmuxMioOut::Ioa6,
    PinmuxMioOut::Ioa7,
    PinmuxMioOut::Ioa8,
    PinmuxMioOut::Iob9,
    PinmuxMioOut::Iob10,
    PinmuxMioOut::Iob11,
    PinmuxMioOut::Iob12,
    PinmuxMioOut::Ioc10,
    PinmuxMioOut::Ioc11,
    PinmuxMioOut::Ioc12,
    PinmuxMioOut::Ior10,
    PinmuxMioOut::Ior11,
    PinmuxMioOut::Ior12,
    PinmuxMioOut::Ior13,
];

static SUPPORTS_VIRT_OD: [PinmuxMioOut; 33] = [
    PinmuxMioOut::Ioa0,
    PinmuxMioOut::Ioa1,
    PinmuxMioOut::Ioa2,
    PinmuxMioOut::Ioa3,
    PinmuxMioOut::Ioa4,
    PinmuxMioOut::Ioa5,
    PinmuxMioOut::Iob0,
    PinmuxMioOut::Iob1,
    PinmuxMioOut::Iob2,
    PinmuxMioOut::Iob3,
    PinmuxMioOut::Iob4,
    PinmuxMioOut::Iob5,
    PinmuxMioOut::Iob6,
    PinmuxMioOut::Iob7,
    PinmuxMioOut::Iob8,
    PinmuxMioOut::Ioc0,
    PinmuxMioOut::Ioc1,
    PinmuxMioOut::Ioc2,
    PinmuxMioOut::Ioc3,
    PinmuxMioOut::Ioc4,
    PinmuxMioOut::Ioc5,
    PinmuxMioOut::Ioc6,
    PinmuxMioOut::Ioc7,
    PinmuxMioOut::Ioc8,
    PinmuxMioOut::Ioc9,
    PinmuxMioOut::Ior0,
    PinmuxMioOut::Ior1,
    PinmuxMioOut::Ior2,
    PinmuxMioOut::Ior3,
    PinmuxMioOut::Ior4,
    PinmuxMioOut::Ior5,
    PinmuxMioOut::Ior6,
    PinmuxMioOut::Ior7,
];

fn write_all_verify(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    write: u32,
    read: u32,
    config: &HashMap<PinmuxMioOut, PinmuxOutsel>,
) -> Result<()> {
    let mask = config.values().fold(0, |acc, v| {
        let i = u32::from(*v) - u32::from(PinmuxOutsel::Gpio0Gpio0);
        acc | 1u32 << i
    });

    let (masked_write, masked_read) = (write & mask, read & mask);

    log::info!(
        "write & verify pattern {write:08x} with mask {mask:08x}: {masked_write:08x} -> {masked_read:08x}"
    );

    if masked_write == 0 {
        log::info!(
            "skipping: {masked_write:08x} has no bits in common with the pinmux configuration"
        );
        return Ok(());
    }

    GpioSet::write_all(uart, masked_write)?;

    let mut result = 0u32;
    for (k, v) in config.iter() {
        let n = u32::from(transport.gpio_pin(&k.to_string())?.read()?);
        let i = u32::from(*v) - u32::from(PinmuxOutsel::Gpio0Gpio0);
        result |= n << i;
    }

    log::info!("result = {result:08x}");
    assert_eq!(masked_read, result);

    Ok(())
}

fn read_all_verify(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    write: u32,
    read: u32,
    config: &HashMap<PinmuxPeripheralIn, PinmuxInsel>,
) -> Result<()> {
    let mask = config.keys().fold(0, |acc, k| {
        let i = u32::from(*k) - u32::from(PinmuxPeripheralIn::Gpio0Gpio0);
        acc | 1u32 << i
    });

    let (masked_write, masked_read) = (write & mask, read & mask);

    log::info!(
        "read & verify pattern with mask {mask:08x}: {masked_write:08x} -> {masked_read:08x}"
    );

    if masked_write == 0 {
        log::info!(
            "skipping: {masked_write:08x} has no bits in common with the pinmux configuration"
        );
        return Ok(());
    }

    for (k, v) in config.iter() {
        let i = u32::from(*k) - u32::from(PinmuxPeripheralIn::Gpio0Gpio0);
        transport
            .gpio_pin(&v.to_string())?
            .write((masked_write >> i) & 1 != 0)?;
    }

    let result = GpioGet::read_all(uart)? & mask;
    log::info!("result = {result:08x}");
    assert_eq!(masked_read, result);

    Ok(())
}

fn get_config(transport: &TransportWrapper) -> Config {
    let gpio_pins = transport.gpios();
    let pinmux_insels = gpio_pins
        .iter()
        .map(|pin| PinmuxInsel::from_str(pin).unwrap());
    let pinmux_mio_outs = gpio_pins
        .iter()
        .map(|pin| PinmuxMioOut::from_str(pin).unwrap());
    let gpio_inputs = GPIOS.iter().map(|(input, _)| *input);
    let gpio_outputs = GPIOS.iter().map(|(_, output)| *output);

    let input: HashMap<_, _> = iter::zip(gpio_inputs, pinmux_insels).collect();
    let output: HashMap<_, _> = iter::zip(pinmux_mio_outs, gpio_outputs).collect();

    Config { input, output }
}

fn test_gpio_outputs(transport: &TransportWrapper, config: &Config) -> Result<()> {
    let uart = transport.uart("console")?;
    PinmuxConfig::configure(&*uart, None, Some(&config.output), None)?;

    log::info!("Configuring debugger GPIOs as inputs");
    // The outputs (with respect to pinmux config) correspond to the input pins on the debug board.
    for pin in config.output.keys() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::Input)?;
    }

    log::info!("Enabling outputs on the DUT");
    GpioSet::set_enabled_all(&*uart, 0xFFFFFFFF)?;
    write_all_verify(transport, &*uart, 0x5555_5555, 0x5555_5555, &config.output)?;
    write_all_verify(transport, &*uart, 0xAAAA_AAAA, 0xAAAA_AAAA, &config.output)?;

    for i in 0..32 {
        write_all_verify(transport, &*uart, 1 << i, 1 << i, &config.output)?;
    }

    Ok(())
}

fn test_gpio_inputs(transport: &TransportWrapper, config: &Config) -> Result<()> {
    let uart = transport.uart("console")?;

    PinmuxConfig::configure(&*uart, Some(&config.input), None, None)?;

    log::info!("Configuring debugger GPIOs as outputs");
    // The inputs (with respect to pinmux config) correspond to the output pins on the debug board.
    for pin in config.input.values() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::PushPull)?;
    }

    log::info!("Disabling outputs on the DUT");
    GpioSet::set_enabled_all(&*uart, 0x0)?;

    read_all_verify(transport, &*uart, 0x5555_5555, 0x5555_5555, &config.input)?;
    read_all_verify(transport, &*uart, 0xAAAA_AAAA, 0xAAAA_AAAA, &config.input)?;

    for i in 0..32 {
        read_all_verify(transport, &*uart, 1 << i, 1 << i, &config.input)?;
    }
    Ok(())
}

fn test_pad_inversion(transport: &TransportWrapper, config: &Config) -> Result<()> {
    let uart = transport.uart("console")?;

    let invert_all: HashMap<_, _> = config
        .output
        .keys()
        .map(|&mio| (mio, PinmuxPadAttr::INVERT))
        .collect();

    log::info!("Configuring pads as inverted inputs");
    PinmuxConfig::configure(&*uart, Some(&config.input), None, Some(&invert_all))?;

    log::info!("Configuring debugger GPIOs as outputs");
    // The inputs (with respect to pinmux config) correspond to the output pins on the debug board.
    for pin in config.input.values() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::PushPull)?;
    }

    log::info!("Disabling outputs on the DUT");
    GpioSet::set_enabled_all(&*uart, 0x0)?;

    log::info!("Testing inverted device inputs");
    read_all_verify(transport, &*uart, 0x5555_5555, !0x5555_5555, &config.input)?;
    read_all_verify(transport, &*uart, 0xAAAA_AAAA, !0xAAAA_AAAA, &config.input)?;

    for i in 0..32 {
        read_all_verify(transport, &*uart, 1 << i, !(1 << i), &config.input)?;
    }

    log::info!("Configuring pads as inverted outputs");
    PinmuxConfig::configure(&*uart, None, Some(&config.output), Some(&invert_all))?;

    log::info!("Configuring debugger GPIOs as inputs");
    // The outputs (with respect to pinmux config) correspond to the input pins on the debug board.
    for pin in config.output.keys() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::Input)?;
    }

    log::info!("Enabling outputs on the DUT");
    GpioSet::set_enabled_all(&*uart, 0xFFFFFFFF)?;

    log::info!("Testing inverted device outputs");
    write_all_verify(transport, &*uart, 0x5555_5555, !0x5555_5555, &config.output)?;
    write_all_verify(transport, &*uart, 0xAAAA_AAAA, !0xAAAA_AAAA, &config.output)?;

    for i in 0..32 {
        write_all_verify(transport, &*uart, 1 << i, !(1 << i), &config.output)?;
    }

    Ok(())
}

/// Test opendrain feature of pads.
///
/// Both normal and virtual opendrain can be tested by passing a different set
/// of pad filters and the correct pad attribute to apply.
fn test_opendrain(
    transport: &TransportWrapper,
    config: &Config,
    pad_filter: &[PinmuxMioOut],
    pad_attr: PinmuxPadAttr,
) -> Result<()> {
    let uart = transport.uart("console")?;

    log::info!("Configuring debugger GPIOs as pulled-up inputs");
    // The inputs (with respect to pinmux config) correspond to the output pins on the debug board.
    let opendrain_inputs = config.input.values();
    for pin in opendrain_inputs {
        let pin = transport.gpio_pin(&pin.to_string())?;
        pin.set(Some(PinMode::Input), None, Some(PullMode::PullUp), None)?;
    }

    // Filter pads to those supporting opendrain using the provided filter.
    let opendrain_outputs: HashMap<_, _> = config
        .output
        .clone()
        .into_iter()
        .filter(|&(mio, _)| pad_filter.contains(&mio))
        .collect();
    let opendrain_attrs: HashMap<_, _> = opendrain_outputs
        .keys()
        .map(|&mio| (mio, pad_attr))
        .collect();

    log::info!("Configuring pads as opendrain outputs");
    PinmuxConfig::configure(
        &*uart,
        None,
        Some(&opendrain_outputs),
        Some(&opendrain_attrs),
    )?;

    log::info!("Enabling outputs on the DUT");
    GpioSet::set_enabled_all(&*uart, 0xFFFFFFFF)?;

    log::info!("Testing opendrain device outputs");
    for pattern in [0x5555_5555, 0xAAAA_AAAA] {
        write_all_verify(transport, &*uart, pattern, pattern, &opendrain_outputs)?;
    }
    for i in 0..32 {
        write_all_verify(transport, &*uart, 1 << i, 1 << i, &opendrain_outputs)?;
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let config = get_config(&transport);

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running ", opts.timeout)?;

    execute_test!(test_gpio_outputs, &transport, &config);
    execute_test!(test_gpio_inputs, &transport, &config);
    execute_test!(test_pad_inversion, &transport, &config);
    // Only silicon supports OpenDrain, FPGA does not.
    if opts.init.backend_opts.interface == "teacup" {
        execute_test!(
            test_opendrain,
            &transport,
            &config,
            &SUPPORTS_OD,
            PinmuxPadAttr::OD_EN,
        );
    }
    execute_test!(
        test_opendrain,
        &transport,
        &config,
        &SUPPORTS_VIRT_OD,
        PinmuxPadAttr::VIRTUAL_OD_EN
    );

    Ok(())
}
