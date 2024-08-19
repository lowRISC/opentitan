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
use opentitanlib::test_utils::mem::MemWriteReq;
use opentitanlib::uart::console::UartConsole;
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

    /// Name of the debugger's I2C interface.
    #[arg(long, default_value = "0")]
    i2c: String,

    /// Path to the firmware's ELF file, for querying symbol addresses.
    #[arg(value_name = "FIRMWARE_ELF")]
    firmware_elf: PathBuf,
}

fn test_override(
    opts: &Opts,
    transport: &TransportWrapper,
    gpio_pins: &[Rc<dyn GpioPin>],
    backdoor_start_addr: u32,
    data: u8,
) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let gpio_bitbanging = transport.gpio_bitbanging()?;

    const SAMPLES: usize = 5000;
    let mut samples = vec![0x00; SAMPLES];
    let output = &[0x03; SAMPLES];
    let waveform = Box::new([BitbangEntry::Both(output, &mut samples)]);

    UartConsole::wait_for(
        &*uart,
        r".*SiVal: waiting for commands.*?[^\r\n]*",
        opts.timeout,
    )?;
    MemWriteReq::execute(&*uart, backdoor_start_addr, &[1u8])?;

    gpio_bitbanging.run(
        &gpio_pins
            .iter()
            .map(Rc::borrow)
            .collect::<Vec<&dyn GpioPin>>(),
        Duration::from_micros(10),
        waveform,
    )?;

    let mut i2c_bitbang_decoder =
        test_utils::bitbanging::i2c::decoder::Decoder::<0, 1> { buffer: [0; 256] };
    let decoded = i2c_bitbang_decoder.run(samples)?;

    assert_eq!(
        vec![
            test_utils::bitbanging::i2c::decoder::Transfer::Start,
            test_utils::bitbanging::i2c::decoder::Transfer::Addr {
                addr: data >> 1,
                read: (data & 1) == 1,
                nack: false
            },
            test_utils::bitbanging::i2c::decoder::Transfer::Stop,
        ],
        decoded
    );

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

    let data = test_utils::object::symbol_data(&object, "kBitbangData")?;
    let backdoor_start_addr = test_utils::object::symbol_addr(&object, "backdoor_start")?;

    let gpio_pins = transport.gpio_pins(&["IOA7", "IOA8"].map(str::to_owned))?;
    for pin in &gpio_pins {
        pin.set_mode(PinMode::OpenDrain)?;
    }

    for _ in 0..3 {
        execute_test!(
            test_override,
            &opts,
            &transport,
            &gpio_pins,
            backdoor_start_addr,
            data[0]
        );
    }

    transport.apply_default_configuration(None)?;

    Ok(())
}
