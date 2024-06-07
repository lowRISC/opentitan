// Copyright lowRISC contributors (OpenTitan project).
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

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

struct Config {
    input: HashMap<PinmuxPeripheralIn, PinmuxInsel>,
    output: HashMap<PinmuxMioOut, PinmuxOutsel>,
}

static CONFIG: Lazy<HashMap<&'static str, Config>> = Lazy::new(|| {
    collection! {
         // from:https://github.com/lowRISC/opentitan/
         // blob/master/hw/top_earlgrey/data/pins_cw310_hyperdebug.xdc
        "hyper310" => Config {
            input: collection! {
                // The commented lines represent multi-fuction pins.  These will
                // be added back in when the hyperdebug firmware can set these
                // multifunction pins into GPIO mode.
                // ioc0~2: sw strap0~2
                // ioc5: tap strap1
                // ioc6: pwm ext)_clk
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
                // ioc0~2: sw strap0~2
                // ioc5: tap strap1
                // ioc6: pwm ext)_clk
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
        // Replication of the hyper310 config.
        "teacup" => Config {
            input: collection! {
                PinmuxPeripheralIn::GpioGpio17 => PinmuxInsel::Ioc10,
                PinmuxPeripheralIn::GpioGpio18 => PinmuxInsel::Ioc11,
                PinmuxPeripheralIn::GpioGpio19 => PinmuxInsel::Ioc12,

                PinmuxPeripheralIn::GpioGpio20 => PinmuxInsel::Ior5,
                PinmuxPeripheralIn::GpioGpio21 => PinmuxInsel::Ior6,
                PinmuxPeripheralIn::GpioGpio22 => PinmuxInsel::Ior7,

                PinmuxPeripheralIn::GpioGpio25 => PinmuxInsel::Ior10,
                PinmuxPeripheralIn::GpioGpio26 => PinmuxInsel::Ior11,
                PinmuxPeripheralIn::GpioGpio27 => PinmuxInsel::Ior12,
                PinmuxPeripheralIn::GpioGpio28 => PinmuxInsel::Ior13,
            },
            output: collection! {
                PinmuxMioOut::Ioc10 => PinmuxOutsel::GpioGpio17,
                PinmuxMioOut::Ioc11 => PinmuxOutsel::GpioGpio18,
                PinmuxMioOut::Ioc12 => PinmuxOutsel::GpioGpio19,

                PinmuxMioOut::Ior5 => PinmuxOutsel::GpioGpio20,
                PinmuxMioOut::Ior6 => PinmuxOutsel::GpioGpio21,
                PinmuxMioOut::Ior7 => PinmuxOutsel::GpioGpio22,

                PinmuxMioOut::Ior10 => PinmuxOutsel::GpioGpio25,
                PinmuxMioOut::Ior11 => PinmuxOutsel::GpioGpio26,
                PinmuxMioOut::Ior12 => PinmuxOutsel::GpioGpio27,
                PinmuxMioOut::Ior13 => PinmuxOutsel::GpioGpio28,
            },
        },
    }
});

fn gpio_write(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    value: u32,
    config: &HashMap<PinmuxMioOut, PinmuxOutsel>,
    invert: u8,
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
        // invert == 1: use for walking 0
        // invert == 0: use for walking 1
        let write_val = if invert == 1 {
            !masked_value
        } else {
            masked_value
        };
        GpioSet::write_all(uart, write_val)?;
        let mut result = 0u32;
        for (k, v) in config.iter() {
            let n = u32::from(transport.gpio_pin(&k.to_string())?.read()?);
            let i = u32::from(*v) - u32::from(PinmuxOutsel::GpioGpio0);
            result |= n << i;
        }
        if invert == 1 {
            assert_eq!(write_val & mask, result);
        } else {
            assert_eq!(write_val, result);
        }
        std::thread::sleep(Duration::from_millis(100));
    }
    Ok(())
}

fn gpio_read(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    value: u32,
    config: &HashMap<PinmuxPeripheralIn, PinmuxInsel>,
    invert: u32,
) -> Result<()> {
    let mask = if invert == 1 {
        // all 1 for target pins.
        GpioGet::read_all(uart)?
    } else {
        config.keys().fold(0, |acc, k| {
            let i = u32::from(*k) - u32::from(PinmuxPeripheralIn::GpioGpio0);
            acc | 1u32 << i
        })
    };
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
                .write(((masked_value >> i) & 1) != invert)?;
        }
        // issue dummy read to make sure write complete.
        let _ = GpioGet::read_all(uart)?;
        std::thread::sleep(Duration::from_millis(100));
    }
    Ok(())
}

fn test_gpio_outputs(opts: &Opts, transport: &TransportWrapper, uart: &dyn Uart) -> Result<()> {
    log::info!(
        "Configuring pinmux for {:?}",
        opts.init.backend_opts.interface
    );
    let config = CONFIG
        .get(opts.init.backend_opts.interface.as_str())
        .expect("interface");
    PinmuxConfig::configure(uart, Some(&config.input), Some(&config.output))?;

    log::info!("Configuring debugger GPIOs as inputs");
    // The outputs (with respect to pinmux config) correspond to the input pins on the debug board.
    for pin in config.output.keys() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::Input)?;
    }

    log::info!("Enabling outputs on the DUT");
    GpioSet::set_input_noise_filter(uart, u32::MAX, 1)?;
    GpioSet::set_enabled_all(uart, u32::MAX)?;

    // Output level high test
    GpioSet::irq_set_trigger(uart, u32::MAX, "high".into())?;
    GpioSet::irq_acknowledge_all(uart)?;
    GpioSet::irq_restore_all(uart, u32::MAX)?;
    log::info!("test: output level high test");

    // Walking 1
    for i in 16..30 {
        gpio_write(transport, uart, 1 << i, &config.output, 0)?;
    }
    GpioSet::irq_disable_all(uart, u32::MAX)?;

    // Output Rising Edge test
    GpioSet::irq_set_trigger(uart, u32::MAX, "rising".into())?;
    GpioSet::irq_acknowledge_all(uart)?;
    GpioSet::irq_restore_all(uart, u32::MAX)?;

    log::info!("test: output rising edge test");

    // Walking 1
    for i in 16..30 {
        gpio_write(transport, uart, 1 << i, &config.output, 0)?;
    }
    GpioSet::irq_disable_all(uart, u32::MAX)?;

    // Output level low test
    log::info!("test: output level low test");
    GpioSet::write_all(uart, u32::MAX)?;

    GpioSet::irq_set_trigger(uart, u32::MAX, "low".into())?;
    GpioSet::irq_acknowledge_all(uart)?;
    GpioSet::irq_restore_all(uart, 0x1E7E_0000)?;
    // Walking 0
    for i in 0..32 {
        gpio_write(transport, uart, 1 << i, &config.output, 1)?;
    }
    GpioSet::irq_disable_all(uart, u32::MAX)?;

    // Output Falling Edge test
    log::info!("test: output falling edge test");
    GpioSet::irq_set_trigger(uart, u32::MAX, "falling".into())?;
    GpioSet::irq_acknowledge_all(uart)?;
    GpioSet::irq_restore_all(uart, u32::MAX)?;
    GpioSet::write_all(uart, u32::MAX)?;

    // Walking 0
    for i in 0..32 {
        gpio_write(transport, uart, 1 << i, &config.output, 1)?;
    }
    Ok(())
}

fn test_gpio_inputs(opts: &Opts, transport: &TransportWrapper, uart: &dyn Uart) -> Result<()> {
    log::info!(
        "Configuring pinmux for {:?}",
        opts.init.backend_opts.interface
    );
    let config = CONFIG
        .get(opts.init.backend_opts.interface.as_str())
        .expect("interface");
    PinmuxConfig::configure(uart, Some(&config.input), None)?;

    log::info!("Configuring debugger GPIOs as outputs");
    // The inputs (with respect to pinmux config) correspond to the output pins on the debug board.
    for pin in config.input.values() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::PushPull)?;
    }

    log::info!("Disabling outputs on the DUT");
    GpioSet::set_enabled_all(uart, 0x0)?;
    GpioSet::set_input_noise_filter(uart, u32::MAX, 1)?;

    // Initialize pins to 0
    for pin in config.input.values() {
        transport.gpio_pin(&pin.to_string())?.write(false)?;
    }

    // Input level high test
    log::info!("test: input level high test");
    GpioSet::irq_set_trigger(uart, u32::MAX, "high".into())?;
    GpioSet::irq_acknowledge_all(uart)?;
    GpioSet::irq_restore_all(uart, u32::MAX)?;
    // Walking 1
    for i in 16..30 {
        gpio_read(transport, uart, 1 << i, &config.input, 0)?;
    }
    GpioSet::irq_disable_all(uart, u32::MAX)?;

    // Initialize pins to 0
    for pin in config.input.values() {
        transport.gpio_pin(&pin.to_string())?.write(false)?;
    }
    // Input Rising Edge test
    log::info!("test: input rising edge test");
    GpioSet::irq_set_trigger(uart, u32::MAX, "rising".into())?;
    GpioSet::irq_acknowledge_all(uart)?;
    GpioSet::irq_restore_all(uart, u32::MAX)?;
    // Walking 1
    for i in 16..30 {
        gpio_read(transport, uart, 1 << i, &config.input, 0)?;
    }
    GpioSet::irq_disable_all(uart, u32::MAX)?;

    // Initialize pins to 1
    for pin in config.input.values() {
        transport.gpio_pin(&pin.to_string())?.write(true)?;
    }

    // Input level low test
    log::info!("test: input level low test");
    GpioSet::irq_set_trigger(uart, u32::MAX, "low".into())?;
    GpioSet::irq_acknowledge_all(uart)?;
    GpioSet::irq_restore_all(uart, 0x1E7E_0000)?;
    // Walking 0
    for i in 16..30 {
        gpio_read(transport, uart, 1 << i, &config.input, 1)?;
    }
    GpioSet::irq_disable_all(uart, u32::MAX)?;

    // Initialize pins to 1
    for pin in config.input.values() {
        transport.gpio_pin(&pin.to_string())?.write(true)?;
    }
    // Input Falling Edge test
    log::info!("test: input falling edge test");
    GpioSet::irq_set_trigger(uart, u32::MAX, "falling".into())?;
    GpioSet::irq_acknowledge_all(uart)?;
    GpioSet::irq_restore_all(uart, u32::MAX)?;

    // Walking 0
    for i in 16..30 {
        gpio_read(transport, uart, 1 << i, &config.input, 1)?;
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"gpio_intr_test [^\r\n]*", opts.timeout)?;

    execute_test!(test_gpio_inputs, &opts, &transport, &*uart);
    execute_test!(test_gpio_outputs, &opts, &transport, &*uart);
    Ok(())
}
