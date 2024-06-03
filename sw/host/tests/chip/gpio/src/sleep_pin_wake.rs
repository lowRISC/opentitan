// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
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

fn is_valid_pad(pad: &Pad, interface: &str) -> bool {
    match interface {
        "hyper310" => pad.valid_cw310,
        "teacup" => pad.valid_silicon,
        _ => false,
    }
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
        UartConsole::wait_for(&*uart, r"Pad Selection: (\d) / (\d+)\r\n", opts.timeout)?;
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
