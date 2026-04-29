// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, ensure};
use clap::{Parser, ValueEnum};
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::transport::common::usb::UsbHubOp;
use opentitanlib::uart::console::UartConsole;

use usb::UsbOpts;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console/USB timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    /// USB options.
    #[command(flatten)]
    usb: UsbOpts,

    /// Wake method.
    #[arg(long)]
    wake: WakeMethod,
}

#[derive(Clone, Debug, PartialEq, Eq, ValueEnum)]
enum WakeMethod {
    Reset,
    Disconnect,
}

fn usbdev_aon_wake(opts: &Opts, transport: &TransportWrapper, uart: &dyn Uart) -> Result<()> {
    opts.usb.apply_strappings(transport, true)?;
    // Enable VBUS sense on the board if necessary.
    if opts.usb.vbus_control_available() {
        opts.usb.enable_vbus(transport, true)?;
    }
    // Sense VBUS if available.
    if opts.usb.vbus_sense_available() {
        ensure!(
            opts.usb.vbus_present(transport)?,
            "OT USB does not appear to be connected to a host (VBUS not detected)"
        );
    }

    // Wait for device to appear.
    let (hub, port) = opts.usb.wait_for_device_and_get_parent(opts.timeout)?;

    // Next, we suspend the device by directly accessing the parent hub.
    let _ = UartConsole::wait_for(uart, r"configured, waiting for suspend", opts.timeout)?;
    log::info!("suspend device");
    hub.op(
        UsbHubOp::Suspend,
        port,
        Duration::from_millis(1000),
        !opts.usb.relaxed_hub_op,
    )?;
    let _ = UartConsole::wait_for(uart, r"suspended, waiting for", opts.timeout)?;
    log::info!("device has suspended");

    // While suspended, we issue a bus reset or disconnect.
    match opts.wake {
        WakeMethod::Reset => {
            log::info!("reset device");
            hub.op(
                UsbHubOp::Reset,
                port,
                Duration::from_millis(1000),
                !opts.usb.relaxed_hub_op,
            )?;
            let _ =
                UartConsole::wait_for(uart, r"reset, take control back from aon", opts.timeout)?;
        }
        WakeMethod::Disconnect => {
            log::info!("disconnect device");
            ensure!(
                opts.usb.vbus_control_available(),
                "this test requires VBUS control"
            );
            opts.usb.enable_vbus(transport, false)?;
            if opts.usb.vbus_sense_available() {
                ensure!(
                    !opts.usb.vbus_present(transport)?,
                    "OT USB appears to still be connected to a host (VBUS detected)"
                );
            }
            let _ = UartConsole::wait_for(
                uart,
                r"disconnect, take control back from aon",
                opts.timeout,
            )?;
        }
    }

    let _ = UartConsole::wait_for(uart, r"PASS!", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    let _ = UartConsole::wait_for(&*uart, r"Running ", opts.timeout)?;

    execute_test!(usbdev_aon_wake, &opts, &transport, &*uart);

    Ok(())
}
