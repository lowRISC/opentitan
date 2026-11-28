// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::sync::LazyLock;
use std::time::Duration;

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::gpio::{
    GPIO_INSTANCES, GpioGet, GpioSet, input_pin, output_pin, outsel, peripheral_in,
};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::pinmux_config::PinmuxConfig;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::{collection, execute_test};
use ot_hal::top::earlgrey::{PinmuxInsel, PinmuxMioOut, PinmuxOutsel, PinmuxPeripheralIn};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

#[derive(Clone)]
struct Config {
    input: HashMap<PinmuxPeripheralIn, PinmuxInsel>,
    output: HashMap<PinmuxMioOut, PinmuxOutsel>,
    pins: Vec<u32>,
}

// Although all supported interfaces use the same config, keep a map because:
//  (a) Future interfaces may need different mappings
//  (b) Hyperdebug firmware updates may enable more testing with differences
//  (c) Testing for the presence of a known interface is useful anyway.
//
// In the sparse pinmux every GPIO pin can only reach one pad, see
// fpga_pads::GPIO_PIN_PADS. So the config is a list of pads, and each instance
// tests the pads it reaches. All interfaces use the CW340 pads, the device side
// expects their pins.
static CONFIG: LazyLock<HashMap<&'static str, Vec<PinmuxMioOut>>> = LazyLock::new(|| {
    collection! {
        "hyper310" => fpga_pads::cw340_pads(),
        "hyper340" => fpga_pads::cw340_pads(),
        "teacup" => fpga_pads::cw340_pads(),
    }
});

/// Returns the interface's pin configuration for the given GPIO instance.
fn get_config(opts: &Opts, instance: u8) -> Config {
    let pads = CONFIG
        .get(opts.init.backend_opts.interface.as_str())
        .unwrap_or_else(|| panic!("Unknown interface {:?}", opts.init.backend_opts.interface));
    let mut config = Config {
        input: HashMap::new(),
        output: HashMap::new(),
        pins: Vec::new(),
    };
    for &pad in pads {
        match fpga_pads::gpio_pin_of_pad(pad) {
            Some((i, pin)) if i == instance => {
                // The INSEL value of a pad is its MIO index plus 2.
                config.input.insert(
                    peripheral_in(instance, pin),
                    PinmuxInsel(u32::from(pad) + 2),
                );
                config.output.insert(pad, outsel(instance, pin));
                config.pins.push(pin);
            }
            _ => {}
        }
    }
    config
}

fn gpio_write(
    transport: &TransportWrapper,
    uart: &dyn Uart,
    instance: u8,
    value: u32,
    config: &HashMap<PinmuxMioOut, PinmuxOutsel>,
    invert: u8,
) -> Result<()> {
    let mask = config.values().fold(0, |acc, v| {
        let i = output_pin(*v);
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
        GpioSet::write_all(uart, instance, write_val)?;
        let mut result = 0u32;
        for (k, v) in config.iter() {
            let n = u32::from(transport.gpio_pin(&k.to_string())?.read()?);
            let i = output_pin(*v);
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
    instance: u8,
    value: u32,
    config: &HashMap<PinmuxPeripheralIn, PinmuxInsel>,
    invert: u32,
) -> Result<()> {
    let mask = if invert == 1 {
        // all 1 for target pins.
        GpioGet::read_all(uart, instance)?
    } else {
        config.keys().fold(0, |acc, k| {
            let i = input_pin(*k);
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
            let i = input_pin(*k);
            transport
                .gpio_pin(&v.to_string())?
                .write(((masked_value >> i) & 1) != invert)?;
        }
        // issue dummy read to make sure write complete.
        let _ = GpioGet::read_all(uart, instance)?;
        std::thread::sleep(Duration::from_millis(100));
    }
    Ok(())
}

fn test_gpio_outputs(opts: &Opts, transport: &TransportWrapper, instance: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    log::info!(
        "Configuring pinmux for {:?}",
        opts.init.backend_opts.interface
    );
    let config = get_config(opts, instance);
    let pin_mask = config.pins.iter().fold(0, |acc, &pin| acc | 1u32 << pin);
    PinmuxConfig::configure(&*uart, Some(&config.input), Some(&config.output), None)?;

    log::info!("Configuring debugger GPIOs as inputs");
    // The outputs (with respect to pinmux config) correspond to the input pins on the debug board.
    for pin in config.output.keys() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::Input)?;
    }

    log::info!("Enabling outputs on the DUT");
    GpioSet::set_input_noise_filter(&*uart, instance, u32::MAX, 1)?;
    GpioSet::set_enabled_all(&*uart, instance, u32::MAX)?;

    // Output level high test
    GpioSet::irq_set_trigger(&*uart, instance, u32::MAX, "high".into())?;
    GpioSet::irq_acknowledge_all(&*uart, instance)?;
    GpioSet::irq_restore_all(&*uart, instance, u32::MAX)?;
    log::info!("test: output level high test");

    // Walking 1
    for &i in &config.pins {
        gpio_write(transport, &*uart, instance, 1 << i, &config.output, 0)?;
    }
    GpioSet::irq_disable_all(&*uart, instance, u32::MAX)?;

    // Output Rising Edge test
    GpioSet::irq_set_trigger(&*uart, instance, u32::MAX, "rising".into())?;
    GpioSet::irq_acknowledge_all(&*uart, instance)?;
    GpioSet::irq_restore_all(&*uart, instance, u32::MAX)?;

    log::info!("test: output rising edge test");

    // Walking 1
    for &i in &config.pins {
        gpio_write(transport, &*uart, instance, 1 << i, &config.output, 0)?;
    }
    GpioSet::irq_disable_all(&*uart, instance, u32::MAX)?;

    // Output level low test
    log::info!("test: output level low test");
    GpioSet::write_all(&*uart, instance, u32::MAX)?;

    GpioSet::irq_set_trigger(&*uart, instance, u32::MAX, "low".into())?;
    GpioSet::irq_acknowledge_all(&*uart, instance)?;
    GpioSet::irq_restore_all(&*uart, instance, pin_mask)?;
    // Walking 0
    for i in 0..32 {
        gpio_write(transport, &*uart, instance, 1 << i, &config.output, 1)?;
    }
    GpioSet::irq_disable_all(&*uart, instance, u32::MAX)?;

    // Output Falling Edge test
    log::info!("test: output falling edge test");
    GpioSet::irq_set_trigger(&*uart, instance, u32::MAX, "falling".into())?;
    GpioSet::irq_acknowledge_all(&*uart, instance)?;
    GpioSet::irq_restore_all(&*uart, instance, u32::MAX)?;
    GpioSet::write_all(&*uart, instance, u32::MAX)?;

    // Walking 0
    for i in 0..32 {
        gpio_write(transport, &*uart, instance, 1 << i, &config.output, 1)?;
    }
    Ok(())
}

fn test_gpio_inputs(opts: &Opts, transport: &TransportWrapper, instance: u8) -> Result<()> {
    let uart = transport.uart("console")?;
    log::info!(
        "Configuring pinmux for {:?}",
        opts.init.backend_opts.interface
    );
    let config = get_config(opts, instance);
    let pin_mask = config.pins.iter().fold(0, |acc, &pin| acc | 1u32 << pin);
    PinmuxConfig::configure(&*uart, Some(&config.input), None, None)?;

    log::info!("Configuring debugger GPIOs as outputs");
    // The inputs (with respect to pinmux config) correspond to the output pins on the debug board.
    for pin in config.input.values() {
        transport
            .gpio_pin(&pin.to_string())?
            .set_mode(PinMode::PushPull)?;
    }

    log::info!("Disabling outputs on the DUT");
    GpioSet::set_enabled_all(&*uart, instance, 0x0)?;
    GpioSet::set_input_noise_filter(&*uart, instance, u32::MAX, 1)?;

    // Initialize pins to 0
    for pin in config.input.values() {
        transport.gpio_pin(&pin.to_string())?.write(false)?;
    }

    // Input level high test
    log::info!("test: input level high test");
    GpioSet::irq_set_trigger(&*uart, instance, u32::MAX, "high".into())?;
    GpioSet::irq_acknowledge_all(&*uart, instance)?;
    GpioSet::irq_restore_all(&*uart, instance, u32::MAX)?;
    // Walking 1
    for &i in &config.pins {
        gpio_read(transport, &*uart, instance, 1 << i, &config.input, 0)?;
    }
    GpioSet::irq_disable_all(&*uart, instance, u32::MAX)?;

    // Initialize pins to 0
    for pin in config.input.values() {
        transport.gpio_pin(&pin.to_string())?.write(false)?;
    }
    // Input Rising Edge test
    log::info!("test: input rising edge test");
    GpioSet::irq_set_trigger(&*uart, instance, u32::MAX, "rising".into())?;
    GpioSet::irq_acknowledge_all(&*uart, instance)?;
    GpioSet::irq_restore_all(&*uart, instance, u32::MAX)?;
    // Walking 1
    for &i in &config.pins {
        gpio_read(transport, &*uart, instance, 1 << i, &config.input, 0)?;
    }
    GpioSet::irq_disable_all(&*uart, instance, u32::MAX)?;

    // Initialize pins to 1
    for pin in config.input.values() {
        transport.gpio_pin(&pin.to_string())?.write(true)?;
    }

    // Input level low test
    log::info!("test: input level low test");
    GpioSet::irq_set_trigger(&*uart, instance, u32::MAX, "low".into())?;
    GpioSet::irq_acknowledge_all(&*uart, instance)?;
    GpioSet::irq_restore_all(&*uart, instance, pin_mask)?;
    // Walking 0
    for &i in &config.pins {
        gpio_read(transport, &*uart, instance, 1 << i, &config.input, 1)?;
    }
    GpioSet::irq_disable_all(&*uart, instance, u32::MAX)?;

    // Initialize pins to 1
    for pin in config.input.values() {
        transport.gpio_pin(&pin.to_string())?.write(true)?;
    }
    // Input Falling Edge test
    log::info!("test: input falling edge test");
    GpioSet::irq_set_trigger(&*uart, instance, u32::MAX, "falling".into())?;
    GpioSet::irq_acknowledge_all(&*uart, instance)?;
    GpioSet::irq_restore_all(&*uart, instance, u32::MAX)?;

    // Walking 0
    for &i in &config.pins {
        gpio_read(transport, &*uart, instance, 1 << i, &config.input, 1)?;
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"gpio_intr_test ", opts.timeout)?;

    for instance in 0..GPIO_INSTANCES.len() as u8 {
        log::info!("Testing GPIO instance {instance}");
        execute_test!(test_gpio_inputs, &opts, &transport, instance);
        execute_test!(test_gpio_outputs, &opts, &transport, instance);
        // The pads stay routed to this instance, so stop it from driving them
        // and silence its interrupts before testing the next instance.
        GpioSet::set_enabled_all(&*uart, instance, 0)?;
        GpioSet::irq_disable_all(&*uart, instance, u32::MAX)?;
        GpioSet::irq_acknowledge_all(&*uart, instance)?;
    }
    Ok(())
}
