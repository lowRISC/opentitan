// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This harness controls a number of suspend-sleep-resume USBDEV tests:
// - usbdev_suspend_resume_test
// - usbdev_sleep_resume_test
// - usbdev_sleep_reset_test
// - usbdev_sleep_disconnect_test
// - usbdev_sleep_resume_test
// - usbdev_sleep_reset_test
// - usbdev_sleep_disconnect_test
//
// The above are sub-sections of the following full sequence test:
// - usbdev_suspend_full_test

use anyhow::{anyhow, bail, ensure, Context, Result};
use clap::{Parser, ValueEnum};
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

use usb::{UsbHub, UsbHubOp, UsbOpts};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    // Console/USB timeout; test harness must allow time for device configuration by
    // the host, as well as iterating through a number of test phases.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "60s")]
    timeout: Duration,

    /// USB options.
    #[command(flatten)]
    usb: UsbOpts,

    // Iteration count.
    #[arg(long, default_value = "1")]
    num_iters: u32,

    // Test phases.
    #[arg(long)]
    init_phase: SuspendPhase,
    #[arg(long)]
    fin_phase: SuspendPhase,
}

// Test phases
// - the tests controlled by this sequence presently run a contiguous sequence of phases
//   within this full sequence.
#[derive(Clone, Debug, PartialEq, Eq, ValueEnum, strum::Display)]
enum SuspendPhase {
    // Resume Signaling stimulus when suspended but not in a sleep state.
    Suspend,
    // Resume Signaling when the device is in Normal Sleep
    //  (clocks stopped but USBDEV not powered down).
    SleepResume,
    // Awaken from Normal Sleep in responses to a Bus Reset.
    SleepReset,
    // ... to a VBUS removal (disconnection).
    SleepDisconnect,
    // As for the above tests phases, but entering Deep Sleep rather in which power is removed also.
    DeepResume,
    DeepReset,
    DeepDisconnect,
    // Final test state; device disconnects and test completes.
    Shutdown,
}

// Wait for a device to appear and then return the parent device and port number.
fn wait_for_device_and_get_parent(opts: &Opts) -> Result<(rusb::Device<rusb::Context>, u8)> {
    // Wait for USB device to appear.
    log::info!("waiting for device...");
    let devices = opts.usb.wait_for_device(opts.timeout)?;
    if devices.is_empty() {
        bail!("no USB device found");
    }
    if devices.len() > 1 {
        bail!("several USB devices found");
    }
    let device = &devices[0];
    log::info!(
        "device found at bus={} address={}",
        device.device().bus_number(),
        device.device().address()
    );

    // Important note: here the handle will be dropped and the device handle
    // will be closed.
    Ok((
        device
            .device()
            .get_parent()
            .context("device has no parent, you need to connect it via a hub for this test")?,
        device.device().port_number(),
    ))
}

// Delay for the specified number of USB milliseconds (= bus frames).
fn delay_millis(frames: u64) {
    std::thread::sleep(Duration::from_millis(frames));
}

// Time intervals, in milliseconds.
// - These are determined by the USB 2.0 Protocol specification.
const TIME_SUSPENDING: u64 = 4;
const TIME_RESUMING: u64 = 20;
const TIME_RESETTING: u64 = 10;

fn suspend(hub: &UsbHub, port: u8) -> Result<()> {
    log::info!("suspending port {}", port);
    hub.op(UsbHubOp::Suspend, port, Duration::from_millis(100))?;
    // Device shall suspend after 3ms of Idle state.
    delay_millis(TIME_SUSPENDING);
    log::info!("suspended");
    Ok(())
}

fn resume(hub: &UsbHub, port: u8) -> Result<()> {
    log::info!("resuming device on port {}", port);
    hub.op(UsbHubOp::Resume, port, Duration::from_millis(100))?;
    // Resume Signaling shall be performed for at least 20ms.
    delay_millis(TIME_RESUMING);
    log::info!("resumed");
    Ok(())
}

fn reset(hub: &UsbHub, port: u8) -> Result<()> {
    log::info!("resetting device on port {}", port);
    // Reset Signaling shall be performed for at least 10ms.
    hub.op(UsbHubOp::Reset, port, Duration::from_millis(100))?;
    delay_millis(TIME_RESETTING);
    log::info!("reset");
    Ok(())
}

fn connect(usb: &UsbOpts, transport: &TransportWrapper) -> Result<()> {
    log::info!("connecting device");
    usb.enable_vbus(transport, true)?;
    log::info!("connected");
    Ok(())
}

fn disconnect(usb: &UsbOpts, transport: &TransportWrapper) -> Result<()> {
    log::info!("disconnecting device");
    usb.enable_vbus(transport, false)?;
    log::info!("disconnected");
    Ok(())
}

// Implements the host-side component of usbdev_suspend_<>_test
fn usbdev_suspend(
    opts: &Opts,
    transport: &TransportWrapper,
    uart: &dyn Uart,
) -> Result<(), anyhow::Error> {
    // - These impact successful operation of the device-side software; vary them appreciably
    //   and test failures may occur through device-side timeout or the device not being ready.
    let time_suspended_short: u64 = 3;
    let time_suspended_long: u64 = 50;

    // - Fairly arbitrary, may be modified quite freely.
    let time_disconnected: u64 = 1000;

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
    let (parent, port) = wait_for_device_and_get_parent(opts)?;
    log::info!(
        "parent hub at bus={}, address={}, port numbers={:?}",
        parent.bus_number(),
        parent.address(),
        parent.port_numbers()?
    );
    log::info!("device under test is on port {}", port);
    // At this point, we are not holding any device handle. If we really want to make sure,
    // we could unbind the device from the driver but this requires a lot of privileges.

    let _devices = opts.usb.wait_for_device(opts.timeout)?;

    let hub = UsbHub::from_device(&parent).context("for this test, you need to make sure that the program has sufficient permissions to access the hub")?;

    // Collect test phases.
    let init_phase = opts.init_phase.clone();
    let fin_phase = opts.fin_phase.clone();

    // The full suspend-sleep-resume testing is decomposed into a number of shorter sequences to
    // make chip-level simulation feasible. Most of the top-level tests that this harness supports
    // expects to run through a short sub-sequence of these test phases.
    log::info!("Phase sequence - {} to {} inclusive", init_phase, fin_phase);

    for iter in 1..=opts.num_iters {
        log::info!("Iteration {} of {}", iter, opts.num_iters);
        let mut phase = init_phase.clone();
        loop {
            log::info!("Test phase {}", phase);

            // Synchronize with the device-side code; it shall always emit this message at the point
            // of being ready to receive the stimulus within a given test phase, because we have
            // neither this harness nor the device-side code has any control over how long it takes
            // the host to detect and configure the device.
            UartConsole::wait_for(uart, r"Phase awaiting stimulus", opts.timeout)?;

            // All phase require a Suspend request and then wait for > 3 frames; some phases require
            // a longer delay so that the device-side code decides to enter a sleep state.
            suspend(&hub, port)?;
            if phase == SuspendPhase::Suspend {
                delay_millis(time_suspended_short);
            } else {
                // Longer Suspended state, a cue to enter the sleep state.
                delay_millis(time_suspended_long);
            }

            // Next test phase; initialize to final phase (safer default than the current phase).
            let mut next_phase = fin_phase.clone();
            match phase {
                // Basic test of Suspend-Resume functionality without entering a sleep state.
                SuspendPhase::Suspend => {
                    resume(&hub, port)?;
                    delay_millis(10);
                    next_phase = SuspendPhase::SleepResume;
                }
                // Suspend, enter Normal Sleep, and then awaken in response to Resume signaling.
                SuspendPhase::SleepResume => {
                    resume(&hub, port)?;
                    next_phase = SuspendPhase::SleepReset;
                }
                // Suspend, enter Normal Sleep, and then awaken in response to a Bus Reset.
                SuspendPhase::SleepReset => {
                    reset(&hub, port)?;
                    next_phase = SuspendPhase::SleepDisconnect;
                }
                // Suspend, enter Normal Sleep, and then awaken in response to a VBUS Disconnection.
                SuspendPhase::SleepDisconnect => {
                    if opts.usb.vbus_control_available() {
                        disconnect(&opts.usb, transport)?;
                        delay_millis(time_disconnected);
                        connect(&opts.usb, transport)?;
                    } else {
                        log::info!("Skipping VBUS Disconnection because support unavailable");
                        resume(&hub, port)?;
                    }
                    next_phase = SuspendPhase::DeepResume;
                }
                // Suspend, enter Deep Sleep, and then awaken in response to Resume Signaling.
                SuspendPhase::DeepResume => {
                    resume(&hub, port)?;
                    next_phase = SuspendPhase::DeepReset;
                }
                // Suspend, enter Deep Sleep, and then awaken in response to a Bus Reset.
                SuspendPhase::DeepReset => {
                    reset(&hub, port)?;
                    next_phase = SuspendPhase::DeepDisconnect;
                }
                // Suspend, enter Deep Sleep, and then awaken in response to a VBUS Disconnection.
                SuspendPhase::DeepDisconnect => {
                    if opts.usb.vbus_control_available() {
                        disconnect(&opts.usb, transport)?;
                        delay_millis(time_disconnected);
                        connect(&opts.usb, transport)?;
                    } else {
                        log::info!("Skipping VBUS Disconnection because support unavailable");
                        resume(&hub, port)?;
                    }
                    next_phase = SuspendPhase::Shutdown;
                }
                // Shutdown
                SuspendPhase::Shutdown => {
                    // Nothing or us to do, though we could spot the device disconnection.
                }
            }
            // Have we completed the final phase of the sequence to be tested?
            if phase == fin_phase {
                break;
            }
            phase = next_phase;
        }
    }

    log::info!("Awaiting verdict from device software");

    // Simply await the PASS/FAIL indication from the device-side software.
    let vec = UartConsole::wait_for(uart, r"(PASS|FAIL)!", opts.timeout)?;
    match vec[0].as_str() {
        "PASS!" => Ok(()),
        _ => Err(anyhow!("Failure result: {:?}", vec)),
    }
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Wait until test is running.
    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    execute_test!(usbdev_suspend, &opts, &transport, &*uart);
    Ok(())
}
