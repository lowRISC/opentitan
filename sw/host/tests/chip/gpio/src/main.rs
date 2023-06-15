// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::gpio::{GpioGet, GpioSet};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::pinmux_config::PinmuxConfig;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::{collection, execute_test};

use opentitanlib::chip::autogen::earlgrey::{
    PinmuxInsel, PinmuxMioOut, PinmuxOutsel, PinmuxPeripheralIn,
};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(
        long,
        value_parser = humantime::parse_duration,
        default_value = "600s",
        help = "Console receive timeout",
    )]
    timeout: Duration,
}

struct Config {
    input: HashMap<PinmuxPeripheralIn, PinmuxInsel>,
    output: HashMap<PinmuxMioOut, PinmuxOutsel>,
}

static CONFIG: Lazy<HashMap<&'static str, Config>> = Lazy::new(|| {
    collection! {
        "verilator" => Config {
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
        },
        "hyper310" => Config {
            input: collection! {
                // The commented lines represent multi-fuction pins.  These will
                // be added back in when the hyperdebug firmware can set these
                // multifunction pins into GPIO mode.

                //PinmuxPeripheralIn::GpioGpio0 => PinmuxInsel::Ioa0,   // UART4
                //PinmuxPeripheralIn::GpioGpio1 => PinmuxInsel::Ioa1,   // UART4
                PinmuxPeripheralIn::GpioGpio2 => PinmuxInsel::Ioa2,
                PinmuxPeripheralIn::GpioGpio3 => PinmuxInsel::Ioa3,
                //PinmuxPeripheralIn::GpioGpio4 => PinmuxInsel::Ioa4,   // UART5
                //PinmuxPeripheralIn::GpioGpio5 => PinmuxInsel::Ioa5,   // UART5
                PinmuxPeripheralIn::GpioGpio6 => PinmuxInsel::Ioa6,
                //PinmuxPeripheralIn::GpioGpio7 => PinmuxInsel::Ioa7,   // I2C1
                //PinmuxPeripheralIn::GpioGpio8 => PinmuxInsel::Ioa8,   // I2C1
                //PinmuxPeripheralIn::GpioGpio9 => PinmuxInsel::Iob4,   // UART3
                //PinmuxPeripheralIn::GpioGpio10 => PinmuxInsel::Iob5,  // UART3
                PinmuxPeripheralIn::GpioGpio11 => PinmuxInsel::Iob6,

                PinmuxPeripheralIn::GpioGpio12 => PinmuxInsel::Ioc0,
                PinmuxPeripheralIn::GpioGpio13 => PinmuxInsel::Ioc1,
                PinmuxPeripheralIn::GpioGpio14 => PinmuxInsel::Ioc2,

                PinmuxPeripheralIn::GpioGpio15 => PinmuxInsel::Ioc5,
                PinmuxPeripheralIn::GpioGpio16 => PinmuxInsel::Ioc6,
                PinmuxPeripheralIn::GpioGpio17 => PinmuxInsel::Ioc10,
                PinmuxPeripheralIn::GpioGpio18 => PinmuxInsel::Ioc11,
                PinmuxPeripheralIn::GpioGpio19 => PinmuxInsel::Ioc12,

                PinmuxPeripheralIn::GpioGpio20 => PinmuxInsel::Ior5,
                PinmuxPeripheralIn::GpioGpio21 => PinmuxInsel::Ior6,
                PinmuxPeripheralIn::GpioGpio22 => PinmuxInsel::Ior7,
                // IOR8-9 aren't MIOs.
                PinmuxPeripheralIn::GpioGpio25 => PinmuxInsel::Ior10,
                PinmuxPeripheralIn::GpioGpio26 => PinmuxInsel::Ior11,
                PinmuxPeripheralIn::GpioGpio27 => PinmuxInsel::Ior12,
                PinmuxPeripheralIn::GpioGpio28 => PinmuxInsel::Ior13,

            },
            output: collection! {
                // The commented lines represent multi-fuction pins.  These will
                // be added back in when the hyperdebug firmware can set these
                // multifunction pins into GPIO mode.

                //PinmuxMioOut::Ioa0 => PinmuxOutsel::GpioGpio0,   // UART4
                //PinmuxMioOut::Ioa1 => PinmuxOutsel::GpioGpio1,   // UART4
                PinmuxMioOut::Ioa2 => PinmuxOutsel::GpioGpio2,
                PinmuxMioOut::Ioa3 => PinmuxOutsel::GpioGpio3,
                //PinmuxMioOut::Ioa4 => PinmuxOutsel::GpioGpio4,   // UART5
                //PinmuxMioOut::Ioa5 => PinmuxOutsel::GpioGpio5,   // UART5
                PinmuxMioOut::Ioa6 => PinmuxOutsel::GpioGpio6,
                //PinmuxMioOut::Ioa7 => PinmuxOutsel::GpioGpio7,   // I2C1
                //PinmuxMioOut::Ioa8 => PinmuxOutsel::GpioGpio8,   // I2C1
                //PinmuxMioOut::Iob4 => PinmuxOutsel::GpioGpio9,   // UART3
                //PinmuxMioOut::Iob5 => PinmuxOutsel::GpioGpio10,  // UART3
                PinmuxMioOut::Iob6 => PinmuxOutsel::GpioGpio11,
                PinmuxMioOut::Ioc0 => PinmuxOutsel::GpioGpio12,
                PinmuxMioOut::Ioc1 => PinmuxOutsel::GpioGpio13,
                PinmuxMioOut::Ioc2 => PinmuxOutsel::GpioGpio14,
                PinmuxMioOut::Ioc5 => PinmuxOutsel::GpioGpio15,
                PinmuxMioOut::Ioc6 => PinmuxOutsel::GpioGpio16,
                PinmuxMioOut::Ioc10 => PinmuxOutsel::GpioGpio17,
                PinmuxMioOut::Ioc11 => PinmuxOutsel::GpioGpio18,
                PinmuxMioOut::Ioc12 => PinmuxOutsel::GpioGpio19,
                PinmuxMioOut::Ior5 => PinmuxOutsel::GpioGpio20,
                PinmuxMioOut::Ior6 => PinmuxOutsel::GpioGpio21,
                PinmuxMioOut::Ior7 => PinmuxOutsel::GpioGpio22,
                // IOR8-9 aren't MIOs.
                PinmuxMioOut::Ior10 => PinmuxOutsel::GpioGpio25,
                PinmuxMioOut::Ior11 => PinmuxOutsel::GpioGpio26,
                PinmuxMioOut::Ior12 => PinmuxOutsel::GpioGpio27,
                PinmuxMioOut::Ior13 => PinmuxOutsel::GpioGpio28,
            },
        },
    }
});

fn write_all_verify(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    value: u32,
    config: &HashMap<PinmuxMioOut, PinmuxOutsel>,
) -> Result<()> {
    let mask = config.values().fold(0, |acc, v| {
        let i = u32::from(*v) - u32::from(PinmuxOutsel::GpioGpio0);
        acc | 1u32 << i
    });
    let masked_value = value & mask;
    log::info!(
        "write & verify pattern: {:08x} & {:08x} -> {:08x}",
        value,
        mask,
        masked_value
    );
    if masked_value == 0 {
        log::info!(
            "skipping: {:08x} has no bits in common with the pinmux configuration",
            value
        );
    } else {
        GpioSet::write_all(uart, masked_value)?;
        let mut result = 0u32;
        for (k, v) in config.iter() {
            let n = u32::from(transport.gpio_pin(&k.to_string())?.read()?);
            let i = u32::from(*v) - u32::from(PinmuxOutsel::GpioGpio0);
            result |= n << i;
        }
        log::info!("result = {:08x}", result);
        assert_eq!(masked_value, result);
    }
    Ok(())
}

fn read_all_verify(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    value: u32,
    config: &HashMap<PinmuxPeripheralIn, PinmuxInsel>,
) -> Result<()> {
    let mask = config.keys().fold(0, |acc, k| {
        let i = u32::from(*k) - u32::from(PinmuxPeripheralIn::GpioGpio0);
        acc | 1u32 << i
    });
    let masked_value = value & mask;
    log::info!(
        "read & verify pattern: {:08x} & {:08x} -> {:08x}",
        value,
        mask,
        masked_value
    );
    if masked_value == 0 {
        log::info!(
            "skipping: {:08x} has no bits in common with the pinmux configuration",
            value
        );
    } else {
        for (k, v) in config.iter() {
            let i = u32::from(*k) - u32::from(PinmuxPeripheralIn::GpioGpio0);
            transport
                .gpio_pin(&v.to_string())?
                .write((masked_value >> i) & 1 != 0)?;
        }
        let result = GpioGet::read_all(uart)? & mask;
        log::info!("result = {:08x}", result);
        assert_eq!(masked_value, result);
    }
    Ok(())
}

fn test_gpio_outputs(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    log::info!(
        "Configuring pinmux for {:?}",
        opts.init.backend_opts.interface
    );
    let config = CONFIG
        .get(opts.init.backend_opts.interface.as_str())
        .expect("interface");
    PinmuxConfig::configure(&*uart, None, Some(&config.output))?;

    log::info!("Configuring debugger GPIOs as inputs");
    // The outputs (with respect to pinmux config) correspond to the input pins on the debug board.
    for pin in config.output.keys() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::Input)?;
    }

    log::info!("Enabling outputs on the DUT");
    GpioSet::set_enabled_all(&*uart, 0xFFFFFFFF)?;
    write_all_verify(transport, &*uart, 0x5555_5555, &config.output)?;
    write_all_verify(transport, &*uart, 0xAAAA_AAAA, &config.output)?;

    for i in 0..32 {
        write_all_verify(transport, &*uart, 1 << i, &config.output)?;
    }
    Ok(())
}

fn test_gpio_inputs(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    log::info!(
        "Configuring pinmux for {:?}",
        opts.init.backend_opts.interface
    );
    let config = CONFIG
        .get(opts.init.backend_opts.interface.as_str())
        .expect("interface");
    PinmuxConfig::configure(&*uart, Some(&config.input), None)?;

    log::info!("Configuring debugger GPIOs as outputs");
    // The inputs (with respect to pinmux config) correspond to the output pins on the debug board.
    for pin in config.input.values() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::PushPull)?;
    }

    log::info!("Disabling outputs on the DUT");
    GpioSet::set_enabled_all(&*uart, 0x0)?;

    read_all_verify(transport, &*uart, 0x5555_5555, &config.input)?;
    read_all_verify(transport, &*uart, 0xAAAA_AAAA, &config.input)?;

    for i in 0..32 {
        read_all_verify(transport, &*uart, 1 << i, &config.input)?;
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(test_gpio_outputs, &opts, &transport);
    execute_test!(test_gpio_inputs, &opts, &transport);
    Ok(())
}
