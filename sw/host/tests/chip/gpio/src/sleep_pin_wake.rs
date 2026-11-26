// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use fpga_pads::{MIO_PADS, is_valid_pad};
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::MemWriteReq;
use opentitanlib::uart::console::UartConsole;
use rand::Rng;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

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

fn sleep_pin_wake_test(
    opts: &Opts,
    transport: &TransportWrapper,
    sival_mio_pad_addr: u32,
    sival_wakeup_detector_idx_addr: u32,
    sival_ready_to_sleep_addr: u32,
) -> Result<()> {
    let interface = opts.init.backend_opts.interface.as_str();
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;

    log::info!("Starting host side");

    let detector_match =
        UartConsole::wait_for(&*uart, r"detector (\d+) is selected", opts.timeout)?;
    let detector: usize = detector_match[1].parse()?;

    UartConsole::wait_for(&*uart, "SiVal: waiting for commands", opts.timeout)?;

    let num_valid_pads = MIO_PADS
        .iter()
        .filter(|&x| is_valid_pad(x, interface))
        .count();
    let rand_valid_pad_index = rand::thread_rng().gen_range(0..num_valid_pads);
    let rand_pad_index = MIO_PADS
        .iter()
        .enumerate()
        .filter(|(_, x)| is_valid_pad(x, interface))
        .nth(rand_valid_pad_index)
        .map(|(i, _)| i)
        .unwrap();

    MemWriteReq::execute(&*uart, sival_mio_pad_addr, &[rand_pad_index as u8])?;

    let pad_sel_match =
        UartConsole::wait_for(&*uart, r"Pad Selection: (\d) / (\d+)", opts.timeout)?;
    let pad_sel: usize = pad_sel_match[2].parse()?;
    let wake_pin = transport.gpio_pin(MIO_PADS[pad_sel].name)?;

    wake_pin.set_mode(PinMode::PushPull)?;
    wake_pin.write(false)?; // Don't wake up yet.
    MemWriteReq::execute(&*uart, sival_ready_to_sleep_addr, &[1])?;
    UartConsole::wait_for(&*uart, "Entering low power mode.", opts.timeout)?;
    wake_pin.write(true)?;
    UartConsole::wait_for(&*uart, "Test in post-sleep pin wakeup phase", opts.timeout)?;

    // After the device wakes up from a (possibly deep) sleep, remind it of
    // what wakeup detector it had chosen (and told us about earlier).
    MemWriteReq::execute(&*uart, sival_wakeup_detector_idx_addr, &[detector as u8])?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let elf_binary = fs::read(&opts.firmware_elf)?;
    let elf_file = object::File::parse(&*elf_binary)?;

    let sival_mio_pad_addr = test_utils::object::symbol_addr(&elf_file, "sival_mio_pad")?;
    let sival_wakeup_detector_idx_addr =
        test_utils::object::symbol_addr(&elf_file, "sival_wakeup_detector_idx")?;
    let sival_ready_to_sleep_addr =
        test_utils::object::symbol_addr(&elf_file, "sival_ready_to_sleep")?;

    execute_test!(
        sleep_pin_wake_test,
        &opts,
        &transport,
        sival_mio_pad_addr,
        sival_wakeup_detector_idx_addr,
        sival_ready_to_sleep_addr,
    );
    Ok(())
}
