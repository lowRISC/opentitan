// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::BitbangEntry;
use opentitanlib::io::gpio::GpioPin;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use std::borrow::Borrow;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

fn test_clock_and_duty_cycle(
    transport: &TransportWrapper,
    gpio_pins: &[Rc<dyn GpioPin>],
    period: Duration,
    duty_cycle: f64,
) -> Result<()> {
    let gpio_bitbanging = transport.gpio_bitbanging()?;

    const SAMPLES: usize = 100_000;
    let mut samples = vec![0x00; SAMPLES];
    let mut output = [0x01; SAMPLES];
    output[1] = 0x03;
    output[output.len() - 1] = 0x03;
    let waveform = Box::new([BitbangEntry::Both(&output, &mut samples)]);

    let sampling_period = Duration::from_micros(10);

    gpio_bitbanging.run(
        &gpio_pins
            .iter()
            .map(Rc::borrow)
            .collect::<Vec<&dyn GpioPin>>(),
        sampling_period,
        waveform,
    )?;

    let mut pwm_bitbang_decoder = test_utils::bitbanging::pwm::decoder::Decoder::<0> {
        active_level: test_utils::bitbanging::Bit::High,
        sampling_period,
    };
    let mut decoded = pwm_bitbang_decoder.run(samples)?;
    // Discard the first and the last samples because it may be distorted.
    decoded.pop();
    let count = decoded.len() as f64;
    let (sum_period, sum_duty) = decoded.iter().fold((0.0, 0.0), |(period, duty), elem| {
        (
            period + elem.period.as_micros() as f64,
            duty + elem.duty_cycle as f64,
        )
    });

    let average_period = sum_period / count;
    let average_duty = sum_duty / count;
    let period_error =
        (average_period - period.as_micros() as f64).abs() / period.as_micros() as f64;
    println!(
        "Pwm average period: {} micros, expected: {:?}, err: {}%",
        average_period,
        period,
        period_error * 100.0
    );

    let duty_error = (average_duty - duty_cycle).abs() / duty_cycle;
    println!(
        "Pwm average duty: {}%, expected: {},  err: {}%",
        average_duty,
        duty_cycle,
        duty_error * 100.0
    );

    // The error is explained by the possible values that the clk_div can assume.
    assert!(period_error < 0.02);
    assert!(duty_error < 0.01);

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    transport.pin_strapping("RESET")?.apply()?;
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    uart.clear_rx_buffer()?;
    transport.pin_strapping("RESET")?.remove()?;

    /* Load the ELF binary and get the expect data.*/
    let elf_binary = fs::read(&opts.firmware_elf)?;
    let object = object::File::parse(&*elf_binary)?;

    let clocks = test_utils::object::symbol_data(&object, "kClocksHz")?;
    let duty_cycles = test_utils::object::symbol_data(&object, "kDutyCycles")?;

    //The device uses IOA8 for the pwm, and the host uses the IOA7 to let the device know when the sampling started.
    let gpio_pins = transport.gpio_pins(&["IOA8", "IOA7"].map(str::to_owned))?;
    for pin in &gpio_pins {
        pin.set_mode(PinMode::OpenDrain)?;
    }

    for clock in &clocks {
        for duty_cycle in &duty_cycles {
            println!("Testing clock: {clock}, duty cycle: {duty_cycle}");
            execute_test!(
                test_clock_and_duty_cycle,
                &transport,
                &gpio_pins,
                Duration::from_micros(1_000_000u64 / *clock as u64),
                *duty_cycle as f64,
            );
        }
    }

    transport.apply_default_configuration(None)?;

    Ok(())
}
