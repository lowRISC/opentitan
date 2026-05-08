// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Result, anyhow};
use clap::{Args, Parser, Subcommand};
use std::process::Command;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_log::BootLog;
use opentitanlib::execute_test;
use opentitanlib::rescue::{EntryMode, RescueParams};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(subcommand)]
    command: Commands,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    /// Firmware image
    #[arg(long)]
    firmware: String,
}

/// RescueParams wrapped in a subcommand because its flags conflict with
/// BootstrapOptions from InitializeTest.
#[derive(Debug, Subcommand)]
enum Commands {
    Rescue(UsbRescueParams),
}

/// Override RescueParams with default values for USB DFU protocol.
#[derive(Clone, Debug, Args)]
#[command(mut_arg("protocol", |arg| arg.default_value("usb-dfu")))]
#[command(mut_arg("trigger", |arg| arg.default_value("strap")))]
struct UsbRescueParams {
    #[command(flatten)]
    params: RescueParams,
}

/// Checks that we can use the primitive xmodem tools from the `lrzsz` package
/// to perform firmware rescue.
fn firmware_update_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let Commands::Rescue(rescue_cmd) = &opts.command;
    let rescue = rescue_cmd.params.create(transport)?;

    // It would be even cooler to do this in a python script or shell script, but
    // opentitanlib is just too convenient for manipulating our test infrastructure.
    // We trigger rescue and then use `dfu-util` to perform the actual operation.
    rescue.enter(transport, EntryMode::Reset)?;
    // Note: we drop the rescue instance to release our claim on the usb-dfu
    // interface.  This allows `dfu-util` to claim and use the interface.
    drop(rescue);

    let mut child = Command::new("dfu-util")
        .arg("--device=18d1:023a")
        // AltSetting 0 is the firmware rescue setting.
        .arg("--alt=0")
        .arg("--reset")
        .arg("--download")
        .arg(&opts.firmware)
        .spawn()?;

    let status = child.wait()?;
    log::info!("Got dfu-util exit code {status:?}");

    let capture = UartConsole::wait_for(&*uart, r"PASS!|BFV:([0-9A-Fa-f]{8})", opts.timeout)?;
    if capture[0].starts_with("BFV") {
        Err(anyhow!("Error: {}", capture[0]))
    } else {
        Ok(())
    }
}

/// Checks that we can use the primitive xmodem tools from the `lrzsz` package
/// to perform get the BootLog from the chip.
fn get_boot_log_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let Commands::Rescue(rescue_cmd) = &opts.command;
    let rescue = rescue_cmd.params.create(transport)?;

    let path = format!("boot_log-{}.bin", std::process::id());
    let _ = std::fs::remove_file(&path);
    log::info!("Receving boot_log into {path:?}");

    // It would be even cooler to do this in a python script or shell script, but
    // opentitanlib is just too convenient for manipulating our test infrastructure.
    // We trigger rescue and then use `dfu-util` to perform the actual operation.
    rescue.enter(transport, EntryMode::Reset)?;
    // Note: we drop the rescue instance to release our claim on the usb-dfu
    // interface.  This allows `dfu-util` to claim and use the interface.
    drop(rescue);

    let mut child = Command::new("dfu-util")
        .arg("--device=18d1:023a")
        // AltSetting 3 is the BootLog setting.
        .arg("--alt=3")
        .arg("--upload")
        .arg(&path)
        .spawn()?;

    let status = child.wait()?;
    log::info!("Got dfu-util exit code {status:?}");

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
