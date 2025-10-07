// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Test harness for `i2c_qemu_target_device_test`.
//! This test harness interacts with the memory device emulated by software on
//! opentitan through I2C. The test writes data to the device and reads it
//! back, checking that the returned data from that memory region is the same.

use std::time::Duration;

use clap::Parser;
use opentitanlib::backend::qemu::QemuOpts;
use opentitanlib::io::i2c::Transfer;
use opentitanlib::transport::Transport;
use opentitanlib::transport::qemu::Qemu;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    qemu_opts: QemuOpts,

    #[arg(long, default_value_t)]
    rcfile: String,

    #[arg(long, default_value_t)]
    logging: String,

    #[arg(long, default_value_t)]
    interface: String,
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::parse();
    let qemu = Qemu::from_options(opts.qemu_opts)?;

    let mut monitor = qemu.monitor.borrow_mut();

    let log = qemu.uart("0")?;
    let i2c = qemu.i2c("0")?;

    monitor.cont()?;

    let ready_string = "SYNC: Device Ready";

    // Wait for device to setup and signal ready
    let res = UartConsole::wait_for(&*log, ready_string, Duration::from_secs(60))?;

    match res[0].as_str() {
        x if x == ready_string => (),
        _ => unreachable!(),
    }

    i2c.set_default_address(0x40)?;

    let pointer = 0x30_u8;
    let set_pointer = vec![pointer];

    let write_values: Vec<u8> = (0..16).collect();
    let mut write_buf = set_pointer.clone();
    write_buf.extend(write_values.clone());

    let mut read_buf = [0u8; 16];

    i2c.run_transaction(
        None,
        &mut [
            Transfer::Write(&write_buf),
            Transfer::Write(&set_pointer),
            Transfer::Read(&mut read_buf),
        ],
    )?;

    assert_eq!(&read_buf.as_slice(), &write_values.as_slice());

    Ok(())
}
