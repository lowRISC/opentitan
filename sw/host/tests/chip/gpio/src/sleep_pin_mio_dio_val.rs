// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use clap::Parser;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::gpio::PinMode;
use opentitanlib::io::gpio::PullMode;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

struct Pad {
    name: &'static str,
    valid_cw310: bool,
    valid_silicon: bool,
}

// Valid on CW310: IOR6/7, IOR10-13
// Valid on Silicon: IOA6, IOB6, IOC9-12, IOR5-7, IOR10-13.
#[rustfmt::skip]
const MIO_PADS: &[Pad] = &[
    Pad { name: "IOA0",  valid_cw310: false, valid_silicon: false },  // MIO Pad 0
    Pad { name: "IOA1",  valid_cw310: false, valid_silicon: false },  // MIO Pad 1
    Pad { name: "IOA2",  valid_cw310: false, valid_silicon: false },  // MIO Pad 2
    Pad { name: "IOA3",  valid_cw310: false, valid_silicon: false },  // MIO Pad 3
    Pad { name: "IOA4",  valid_cw310: false, valid_silicon: false },  // MIO Pad 4
    Pad { name: "IOA5",  valid_cw310: false, valid_silicon: false },  // MIO Pad 5
    Pad { name: "IOA6",  valid_cw310: false, valid_silicon: true },   // MIO Pad 6
    Pad { name: "IOA7",  valid_cw310: false, valid_silicon: false },  // MIO Pad 7
    Pad { name: "IOA8",  valid_cw310: false, valid_silicon: false },  // MIO Pad 8
    Pad { name: "IOB0",  valid_cw310: false, valid_silicon: false },  // MIO Pad 9
    Pad { name: "IOB1",  valid_cw310: false, valid_silicon: false },  // MIO Pad 10
    Pad { name: "IOB2",  valid_cw310: false, valid_silicon: false },  // MIO Pad 11
    Pad { name: "IOB3",  valid_cw310: false, valid_silicon: false },  // MIO Pad 12
    Pad { name: "IOB4",  valid_cw310: false, valid_silicon: false },  // MIO Pad 13
    Pad { name: "IOB5",  valid_cw310: false, valid_silicon: false },  // MIO Pad 14
    Pad { name: "IOB6",  valid_cw310: false, valid_silicon: true },   // MIO Pad 15
    Pad { name: "IOB7",  valid_cw310: false, valid_silicon: false },  // MIO Pad 16
    Pad { name: "IOB8",  valid_cw310: false, valid_silicon: false },  // MIO Pad 17
    Pad { name: "IOB9",  valid_cw310: false, valid_silicon: false },  // MIO Pad 18
    Pad { name: "IOB10", valid_cw310: false, valid_silicon: false },  // MIO Pad 19
    Pad { name: "IOB11", valid_cw310: false, valid_silicon: false },  // MIO Pad 20
    Pad { name: "IOB12", valid_cw310: false, valid_silicon: false },  // MIO Pad 21
    Pad { name: "IOC0",  valid_cw310: false, valid_silicon: false },  // MIO Pad 22
    Pad { name: "IOC1",  valid_cw310: false, valid_silicon: false },  // MIO Pad 23
    Pad { name: "IOC2",  valid_cw310: false, valid_silicon: false },  // MIO Pad 24
    Pad { name: "IOC3",  valid_cw310: false, valid_silicon: false },  // MIO Pad 25
    Pad { name: "IOC4",  valid_cw310: false, valid_silicon: false },  // MIO Pad 26
    Pad { name: "IOC5",  valid_cw310: false, valid_silicon: false },  // MIO Pad 27
    Pad { name: "IOC6",  valid_cw310: false, valid_silicon: false },  // MIO Pad 28
    Pad { name: "IOC7",  valid_cw310: false, valid_silicon: false },  // MIO Pad 29
    Pad { name: "IOC8",  valid_cw310: false, valid_silicon: false },  // MIO Pad 30
    Pad { name: "IOC9",  valid_cw310: false, valid_silicon: true },   // MIO Pad 31
    Pad { name: "IOC10", valid_cw310: false, valid_silicon: true },   // MIO Pad 32
    Pad { name: "IOC11", valid_cw310: false, valid_silicon: true },   // MIO Pad 33
    Pad { name: "IOC12", valid_cw310: false, valid_silicon: true },   // MIO Pad 34
    Pad { name: "IOR0",  valid_cw310: false, valid_silicon: false },  // MIO Pad 35
    Pad { name: "IOR1",  valid_cw310: false, valid_silicon: false },  // MIO Pad 36
    Pad { name: "IOR2",  valid_cw310: false, valid_silicon: false },  // MIO Pad 37
    Pad { name: "IOR3",  valid_cw310: false, valid_silicon: false },  // MIO Pad 38
    Pad { name: "IOR4",  valid_cw310: false, valid_silicon: false },  // MIO Pad 39
    Pad { name: "IOR5",  valid_cw310: false, valid_silicon: true },   // MIO Pad 40
    Pad { name: "IOR6",  valid_cw310: true,  valid_silicon: true },   // MIO Pad 41
    Pad { name: "IOR7",  valid_cw310: true,  valid_silicon: true },   // MIO Pad 42
    Pad { name: "IOR10", valid_cw310: true,  valid_silicon: true },   // MIO Pad 43
    Pad { name: "IOR11", valid_cw310: true,  valid_silicon: true },   // MIO Pad 44
    Pad { name: "IOR12", valid_cw310: true,  valid_silicon: true },   // MIO Pad 45
    Pad { name: "IOR13", valid_cw310: true,  valid_silicon: true },   // MIO Pad 46
];

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn is_valid_pad(pad: &Pad, interface: &str) -> bool {
    match interface {
        "hyper310" => pad.valid_cw310,
        "teacup" => pad.valid_silicon,
        _ => false,
    }
}

fn sleep_pin_mio_dio_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let interface = opts.init.backend_opts.interface.as_str();
    let uart = transport.uart("console")?;
    log::info!("Starting host side");

    let mut expected_pin_values: [u8; 47] = [0; 47];
    for _ in 0..MIO_PADS.len() {
        let msg = UartConsole::wait_for(&*uart, r"MIO \[(\d+)\]: (\d+)", opts.timeout)?;
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
