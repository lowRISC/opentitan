// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::collections::HashMap;
use structopt::StructOpt;
use lazy_static::lazy_static;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::io::uart::Uart;
use opentitanlib::{execute_test, collection};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::gpio::{GpioSet, GpioGet};
use opentitanlib::test_utils::pinmux_config::PinmuxConfig;
use opentitanlib::uart::console::UartConsole;

use opentitanlib::chip::earlgrey::{PinmuxPeripheralIn, PinmuxInsel, PinmuxMioOut, PinmuxOutsel};


#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "300s",
        help = "Console receive timeout",
    )]
    timeout: Duration,

}

struct Config {
    input: HashMap<PinmuxPeripheralIn, PinmuxInsel>,
    output: HashMap<PinmuxMioOut, PinmuxOutsel>,
}

lazy_static! {
static ref VERILATOR: Config = Config {
    input: collection! {
        PinmuxPeripheralIn::GpioGpio0 => PinmuxInsel::Iob6,
        PinmuxPeripheralIn::GpioGpio1 => PinmuxInsel::Iob7,
        PinmuxPeripheralIn::GpioGpio2 => PinmuxInsel::Iob8,
        PinmuxPeripheralIn::GpioGpio3 => PinmuxInsel::Iob9,
        PinmuxPeripheralIn::GpioGpio4 => PinmuxInsel::Iob10,
        PinmuxPeripheralIn::GpioGpio5 => PinmuxInsel::Iob11,
        PinmuxPeripheralIn::GpioGpio6 => PinmuxInsel::Iob12,
        PinmuxPeripheralIn::GpioGpio7 => PinmuxInsel::Ior5,
        PinmuxPeripheralIn::GpioGpio8 => PinmuxInsel::Ior6,
        PinmuxPeripheralIn::GpioGpio9 => PinmuxInsel::Ior7,
        // IOR8-9 aren't MIOs.
        PinmuxPeripheralIn::GpioGpio10 => PinmuxInsel::Ior10,
        PinmuxPeripheralIn::GpioGpio11 => PinmuxInsel::Ior11,
        PinmuxPeripheralIn::GpioGpio12 => PinmuxInsel::Ior12,
        PinmuxPeripheralIn::GpioGpio13 => PinmuxInsel::Ior13,
    },
    output: collection! {
        PinmuxMioOut::Iob6 => PinmuxOutsel::GpioGpio0,
        PinmuxMioOut::Iob7 => PinmuxOutsel::GpioGpio1,
        PinmuxMioOut::Iob8 => PinmuxOutsel::GpioGpio2,
        PinmuxMioOut::Iob9 => PinmuxOutsel::GpioGpio3,
        PinmuxMioOut::Iob10 => PinmuxOutsel::GpioGpio4,
        PinmuxMioOut::Iob11 => PinmuxOutsel::GpioGpio5,
        PinmuxMioOut::Iob12 => PinmuxOutsel::GpioGpio6,
        PinmuxMioOut::Ior5 => PinmuxOutsel::GpioGpio7,
        PinmuxMioOut::Ior6 => PinmuxOutsel::GpioGpio8,
        PinmuxMioOut::Ior7 => PinmuxOutsel::GpioGpio9,
        // IOR8-9 aren't MIOs.
        PinmuxMioOut::Ior10 => PinmuxOutsel::GpioGpio10,
        PinmuxMioOut::Ior11 => PinmuxOutsel::GpioGpio11,
        PinmuxMioOut::Ior12 => PinmuxOutsel::GpioGpio12,
        PinmuxMioOut::Ior13 => PinmuxOutsel::GpioGpio13,
    },
};
}

fn write_all_verify(transport: &TransportWrapper, uart: &dyn Uart, value: u32, config: &HashMap<PinmuxMioOut, PinmuxOutsel>) -> Result<()> {
    let mask = config.values().fold(0, |acc, v| {
        let i = u32::from(*v) - u32::from(PinmuxOutsel::GpioGpio0);
        acc | 1u32 << i
    });
    let value = value & mask;
    log::info!("write & verify pattern = {:x?}", value);
    GpioSet::write_all(uart, value)?;
    let mut result = 0u32;
    for (k, v) in config.iter() {
        let n = u32::from(transport.gpio_pin(&k.to_string())?.read()?);
        let i = u32::from(*v) - u32::from(PinmuxOutsel::GpioGpio0);
        result |= n << i;
    }
    assert_eq!(value, result);
    Ok(())
}

fn read_all_verify(transport: &TransportWrapper, uart: &dyn Uart, value: u32, config: &HashMap<PinmuxPeripheralIn, PinmuxInsel>) -> Result<()> {
    let mask = config.keys().fold(0, |acc, k| {
        let i = u32::from(*k) - u32::from(PinmuxPeripheralIn::GpioGpio0);
        acc | 1u32 << i
    });
    let value = value & mask;
    log::info!("read & verify pattern = {:x?}", value);
    for (k, v) in config.iter() {
        let i = u32::from(*k) - u32::from(PinmuxPeripheralIn::GpioGpio0);
        transport.gpio_pin(&v.to_string())?.write((value >> i) & 1 != 0)?;
    }
    std::thread::sleep(Duration::from_secs(10));
    log::info!("sending read_all");
    let result = GpioGet::read_all(uart)? & mask;
    log::info!("read_all = {:?}", result);
    assert_eq!(value, result);
    Ok(())
}

fn test_gpio_outputs(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let config = &VERILATOR;
    log::info!("Configuring pinmux");
    PinmuxConfig::configure(&*uart, None, Some(&config.output))?;
    log::info!("Enabling outputs");
    GpioSet::set_enabled_all(&*uart, 0xFFFFFFFF)?;
    write_all_verify(transport, &*uart, 0x5555_5555, &config.output)?;
    write_all_verify(transport, &*uart, 0xAAAA_AAAA, &config.output)?;
    Ok(())
}

fn test_gpio_inputs(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let config = &VERILATOR;
    log::info!("Configuring pinmux");
    PinmuxConfig::configure(&*uart, Some(&config.input), None)?;
    read_all_verify(transport, &*uart, 0x5555_5555, &config.input)?;
    read_all_verify(transport, &*uart, 0xAAAA_AAAA, &config.input)?;
    Ok(())
}


fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(test_gpio_outputs, &opts, &transport);
    execute_test!(test_gpio_inputs, &opts, &transport);
    Ok(())
}
