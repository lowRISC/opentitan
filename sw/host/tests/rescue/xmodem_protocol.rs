// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Result, anyhow};
use clap::Parser;
use std::process::{Command, Stdio};
use std::rc::Rc;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_log::BootLog;
use opentitanlib::execute_test;
use opentitanlib::rescue::serial::RescueSerial;
use opentitanlib::rescue::{EntryMode, Rescue, RescueMode};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    /// Firmware image
    #[arg(long)]
    firmware: String,
}

/// Checks that we can use the primitive xmodem tools from the `lrzsz` package
/// to perform firmware rescue.
fn firmware_update_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let rescue = RescueSerial::new(Rc::clone(&uart));

    // It would be even cooler to do this in a python script or shell script, but
    // opentitanlib is just too convenient for manipulating our test infrastructure.
    // Nevertheless, we farm out the actual work to the `sx` (send xmodem) command.
    rescue.enter(transport, EntryMode::Reset)?;

    // Get the UART file descriptor and dup it to use as the child's stdin/stdout.
    let fd = uart.borrow_fd()?;
    let stdin = Stdio::from(rustix::io::dup(fd)?);
    let stdout = Stdio::from(rustix::io::dup(fd)?);
    let mut child = Command::new("sx")
        .arg("--1k")
        .arg(&opts.firmware)
        .stdin(stdin)
        .stdout(stdout)
        .spawn()?;

    let status = child.wait()?;
    log::info!("Got xmodem exit code {status:?}");
    rescue.reboot()?;

    let capture = UartConsole::wait_for(&*uart, r"PASS!|BFV:([0-9A-Fa-f]{8})", opts.timeout)?;
    if capture[0].starts_with("BFV") {
        Err(anyhow!("Error: {}", capture[0]))
    } else {
        Ok(())
    }
}

/// Checks that we can use the primitive xmodem tools from the `lrzsz` package
/// to perform get the BootLog from the chip.
fn get_boot_log_test(_opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let rescue = RescueSerial::new(Rc::clone(&uart));

    // It would be even cooler to do this in a python script or shell script, but
    // opentitanlib is just too convenient for manipulating our test infrastructure.
    // Nevertheless, we farm out the actual work to the `rx` (recv xmodem) command.
    rescue.enter(transport, EntryMode::Reset)?;
    rescue.set_mode(RescueMode::BootLog)?;

    let path = format!("boot_log-{}.bin", std::process::id());
    let _ = std::fs::remove_file(&path);
    log::info!("Receving boot_log into {path:?}");

    // Get the UART file descriptor and dup it to use as the child's stdin/stdout.
    let fd = uart.borrow_fd()?;
    let stdin = Stdio::from(rustix::io::dup(fd)?);
    let stdout = Stdio::from(rustix::io::dup(fd)?);
    let mut child = Command::new("rx")
        .arg("--with-crc")
        .arg(&path)
        .stdin(stdin)
        .stdout(stdout)
        .spawn()?;

    let status = child.wait()?;
    log::info!("Got xmodem exit code {status:?}");
    let data = std::fs::read(&path)?;
    let blog = BootLog::try_from(data.as_slice())?;
    log::info!("BootLog = {blog:?}");
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    execute_test!(firmware_update_test, &opts, &transport);
    execute_test!(get_boot_log_test, &opts, &transport);
    Ok(())
}
