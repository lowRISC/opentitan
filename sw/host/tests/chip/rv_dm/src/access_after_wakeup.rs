// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::MemWriteReq;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Path to the ELF file being tested on the device.
    #[arg(long)]
    firmware_elf: PathBuf,
}

fn test_access_after_wakeup(
    opts: &Opts,
    transport: &TransportWrapper,
    software_barrier_addr: u32,
) -> Result<()> {
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let power_button = transport.gpio_pin("Ior13")?;
    power_button.set_mode(PinMode::PushPull)?;
    power_button.write(true)?;

    // Enable console and wait for the message.
    let uart = &*transport.uart("console")?;
    uart.set_flow_control(true)?;
    UartConsole::wait_for(uart, r"Running [^\r\n]*", opts.timeout)?;
    UartConsole::wait_for(uart, r"Software Setup.", opts.timeout)?;

    // Write to progbuf0 and and confirm readback.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?
        .into_raw()?;

    let random_value: u32 = rand::random();
    log::info!("Writing {random_value:#x} to progbuf0");
    jtag.execute(&format!("riscv dmi_write 0x20 {random_value:#x}"))?;

    let readback = u32::from_str_radix(
        jtag.execute("riscv dmi_read 0x20")?
            .trim()
            .trim_start_matches("0x"),
        16,
    )?;
    assert_eq!(random_value, readback);

    // Allow the software to continue execution.
    log::info!("SoftwareBarrier = 1");
    MemWriteReq::execute(uart, software_barrier_addr, &[1])?;

    // Wait for the software to fall asleep.
    UartConsole::wait_for(uart, r"Entering normal sleep.\r\n", opts.timeout)?;

    // Press the power button to wake up the device.
    log::info!("Pushing power button.");
    power_button.write(false)?; // pressing power button

    // Wait for the software to wake up.
    UartConsole::wait_for(uart, r"Waking up from normal sleep.", opts.timeout)?;

    log::info!("Releasing power button.");
    power_button.write(true)?; // releasing power button

    // Check the program bufffer retained the expected value after a normal sleep.
    let readback = u32::from_str_radix(
        jtag.execute("riscv dmi_read 0x20")?
            .trim()
            .trim_start_matches("0x"),
        16,
    )?;
    assert_eq!(random_value, readback);

    // Disconnect JTAG, since after a deep sleep the JTAG agent must be reset to stay synchronized
    // with the design.
    jtag.shutdown()?;

    // Allow the software to continue execution.
    log::info!("SoftwareBarrier = 2");
    MemWriteReq::execute(uart, software_barrier_addr, &[2])?;

    // Wait for the software to fall asleep.
    UartConsole::wait_for(uart, r"Entering deep sleep.\r\n", opts.timeout)?;

    // Press the power button to wake up the device.
    log::info!("Pushing power button.");
    power_button.write(false)?; // pressing power button

    // Wait for the software to wake up.
    UartConsole::wait_for(uart, r"Waking up from deep sleep.", opts.timeout)?;

    log::info!("Releasing power button.");
    power_button.write(true)?; // releasing power button

    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?
        .into_raw()?;

    let random_value: u32 = rand::random();
    log::info!("Writing {random_value:#x} to progbuf0");
    jtag.execute(&format!("riscv dmi_write 0x20 {random_value:#x}"))?;

    let readback = u32::from_str_radix(
        jtag.execute("riscv dmi_read 0x20")?
            .trim()
            .trim_start_matches("0x"),
        16,
    )?;
    assert_eq!(random_value, readback);

    jtag.shutdown()?;

    // Allow the software to continue execution.
    log::info!("SoftwareBarrier = 3");
    MemWriteReq::execute(uart, software_barrier_addr, &[3])?;

    UartConsole::wait_for(uart, r"PASS!", opts.timeout)?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let elf_file = std::fs::read(&opts.firmware_elf).context("failed to read ELF")?;
    let object = object::File::parse(elf_file.as_ref()).context("failed to parse ELF")?;
    let software_barrier_addr = test_utils::object::symbol_addr(&object, "kSoftwareBarrierHost")?;

    execute_test!(
        test_access_after_wakeup,
        &opts,
        &transport,
        software_barrier_addr
    );
    Ok(())
}
