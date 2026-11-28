// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, ensure};
use clap::Parser;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::gpio::PullMode;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

use fpga_pads::{MIO_PADS, is_valid_pad};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn sleep_pin_mio_dio_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let interface = opts.init.backend_opts.interface.as_str();
    let uart = transport.uart("console")?;
    log::info!("Starting host side");

    let mut expected_pin_values = [0u8; MIO_PADS.len()];
    // The device also prints the two constant pads as MIO 0, so read up to the end marker.
    loop {
        let msg = UartConsole::wait_for(
            &*uart,
            r"MIO \[(\d+)\]: (\d+)|END Chosen Retention Types",
            opts.timeout,
        )?;
        if msg[1].is_empty() {
            break;
        }
        let index: usize = msg[1].parse()?;
        expected_pin_values[index] = msg[2].parse()?;
    }

    UartConsole::wait_for(&*uart, r"Going to sleep", opts.timeout)?;

    for (index, pad) in MIO_PADS.iter().enumerate() {
        if is_valid_pad(pad, interface) {
            transport.gpio_pin(pad.name)?.set_mode(PinMode::Input)?;
            let expected_value = expected_pin_values[index];

            // Retention value 0 or 1.
            if expected_value < 2 {
                let pin_value = transport.gpio_pin(pad.name)?.read()? as u8;
                log::info!("Pad {index:?}: expected {expected_value:?}, read {pin_value:?}");
                ensure!(
                    pin_value == expected_value,
                    "Pad {index:?}: expected {expected_value:?}, read {pin_value:?}"
                );
                continue;
            }

            // Retention value High-Z. First test with a pull up.
            transport
                .gpio_pin(pad.name)?
                .set_pull_mode(PullMode::PullDown)?;
            let pin_value = transport.gpio_pin(pad.name)?.read()? as u8;
            log::info!("Pad {index:?}: expected pulled down to 0, read {pin_value:?}");
            ensure!(
                pin_value == 0,
                "Pad {index:?}: expected pulled down to 0, read {pin_value:?}"
            );

            // Next test the same pad/pin with a pull down.
            transport
                .gpio_pin(pad.name)?
                .set_pull_mode(PullMode::PullUp)?;
            let pin_value = transport.gpio_pin(pad.name)?.read()? as u8;
            log::info!("Pad {index:?}: expected pulled up to 1, read {pin_value:?}");
            ensure!(
                pin_value == 1,
                "Pad {index:?}: expected pulled up to 1, read {pin_value:?}"
            );
        }
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(sleep_pin_mio_dio_test, &opts, &transport);
    Ok(())
}
