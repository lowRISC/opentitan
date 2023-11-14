// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use std::str::from_utf8;
use std::thread::sleep;
use std::time::Duration;

use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn send_message(uart: &dyn Uart, msg: &str) -> Result<()> {
    log::info!("Sending (len={}): {}", msg.len(), msg);
    uart.write(msg.as_bytes())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    let uart = transport.uart("console")?;
    UartConsole::wait_for(
        &*uart,
        r"OpenTitan( \(downstream\))? initialisation complete\. Entering main loop",
        opts.timeout,
    )?;

    // Test A: Send a message with all printable ASCII characters each
    // direction. We do host->device first then device->host. The host->device
    // message is padded to 128 bytes, which matches the hardware receive
    // buffer.
    send_message(
        &*uart,
        concat!(
            r##"! "#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_"##,
            r##"`abcdefghijklmnopqrstuvwxyz{|}~Padding to 128 bytes looooooooong"##,
        ),
    )?;
    UartConsole::wait_for(
        &*uart,
        concat!(
            r##"! "#\$%&'\(\)\*\+,-\./0123456789:;<=>\?@ABCDEFGHIJKLMNO"##,
            r##"PQRSTUVWXYZ\[\\\]\^_`abcdefghijklmnopqrstuvwxyz\{\|\}~"##,
        ),
        opts.timeout,
    )?;

    // Test B: Send a message broken into two parts, with a delay between the
    // parts. The app should be able to receive both of these in one read
    // operation.
    send_message(&*uart, "Broken ")?;
    sleep(Duration::from_secs(1));
    send_message(&*uart, "message.")?;

    // Test C: Attempt to send host->device and device->host messages
    // concurrently. host->device messages are in capital letters and
    // device->host messages are in lowercase.
    send_message(&*uart, "ABCDEFGHIJKLMNOPQRSTUVWXYZ")?;
    UartConsole::wait_for(&*uart, "abcdefghijklmnopqrstuvwxyz", opts.timeout)?;
    send_message(&*uart, from_utf8(&[b'A'; 50]).unwrap())?;
    UartConsole::wait_for(&*uart, from_utf8(&[b'a'; 100]).unwrap(), opts.timeout)?;
    send_message(&*uart, from_utf8(&[b'B'; 42]).unwrap())?;
    UartConsole::wait_for(&*uart, from_utf8(&[b'b'; 37]).unwrap(), opts.timeout)?;

    // Verify the device has finished the final receive of test C.
    UartConsole::wait_for(&*uart, "DEVICE DONE.", opts.timeout)?;

    Ok(())
}
