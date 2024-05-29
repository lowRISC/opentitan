// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use clap::Parser;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

use usb::{port_path_string, UsbDeviceHandle, UsbOpts};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console/USB timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "60s")]
    timeout: Duration,

    /// USB options.
    #[command(flatten)]
    usb: UsbOpts,

    /// Do not wait for USB device to appear before continuing with the test.
    #[arg(long, default_value_t = false)]
    no_wait_for_usb_device: bool,

    /// Executable to run after USB device connection.
    /// This harness will spawn a process to execute and continue monitoring the UART
    /// until the test passes (or fails). After that, the process will be killed.
    /// Unless `no_wait_for_usb_device` is set, the harness will pass two extra arguments
    /// to the executable to specify the bus and address of the USB device, as follows:
    /// `--devide <bus>:<addr>`.
    #[arg(long)]
    exec: Option<PathBuf>,

    /// Arguments to pass to the executable.
    #[arg(long)]
    exec_arg: Vec<std::ffi::OsString>,
}

fn wait_for_device(opts: &Opts) -> Result<UsbDeviceHandle> {
    log::info!("waiting for device...");
    let mut devices = opts.usb.wait_for_device(opts.timeout)?;
    if devices.is_empty() {
        bail!("no USB device found");
    }
    if devices.len() > 1 {
        log::error!("several USB devices found:");
        for dev in devices {
            log::error!(
                "- bus={} address={}",
                dev.device().bus_number(),
                dev.device().address()
            );
        }
        bail!("several USB devices found");
    }
    let device = devices.remove(0);
    log::info!(
        "device found at bus={}, address={}, path={}",
        device.device().bus_number(),
        device.device().address(),
        port_path_string(&device.device())?
    );
    Ok(device)
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Wait until test is running.
    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    // Enable VBUS sense on the board if necessary.
    if opts.usb.vbus_control_available() {
        opts.usb.enable_vbus(&transport, true)?;
    }
    // Sense VBUS if available.
    if opts.usb.vbus_sense_available() {
        ensure!(
            opts.usb.vbus_present(&transport)?,
            "OT USB does not appear to be connected to a host (VBUS not detected)"
        );
    }

    // Wait for USB device to appear.
    let device = if opts.no_wait_for_usb_device {
        None
    } else {
        Some(wait_for_device(&opts)?)
    };

    // Run executable if requested.
    let child = match opts.exec {
        Some(exec) => {
            let mut cmd = Command::new(exec);
            if let Some(device) = device {
                cmd.arg("--device").arg(format!(
                    "{}:{}",
                    device.device().bus_number(),
                    device.device().address()
                ));
            }
            cmd.args(opts.exec_arg);
            log::info!(
                "calling {:?} on {:?}",
                cmd.get_program(),
                cmd.get_args().collect::<Vec<_>>()
            );
            Some(cmd.spawn().context("could not start executable")?)
        }
        None => None,
    };

    // Wait for test to pass.
    log::info!("wait for pass...");
    let res = UartConsole::wait_for(&*uart, r"PASS|FAIL", opts.timeout)?;
    match res[0].as_str() {
        "PASS" => (),
        "FAIL" => bail!("device code reported a failure"),
        _ => (),
    };

    // Kill executable (if running).
    if let Some(mut child) = child {
        match child.try_wait() {
            Ok(Some(status)) => log::info!("executable exited with: {status}"),
            Ok(None) => {
                log::info!("executable did not finish and will be killed");
                let _ = child.kill();
            }
            Err(e) => {
                println!("error attempting to get executable status: {e}");
                log::info!("killing executable");
                let _ = child.kill();
            }
        }
    }

    Ok(())
}
