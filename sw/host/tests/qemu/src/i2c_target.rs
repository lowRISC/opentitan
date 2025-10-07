// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Test harness for `i2c_qemu_target_device_test`.
//! This test harness interacts with the memory device emulated by software on
//! opentitan through I2C. The test writes data to the device and reads it
//! back, checking that the returned data from that memory region is the same.
//! To terminate the test on the emulated device side, a magic value is written
//! to a second address, which causes the device to exit the test.

use std::time::Duration;

use anyhow::anyhow;
use clap::Parser;
use opentitanlib::io::i2c::Transfer;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(long, value_parser = humantime::parse_duration, default_value = "60s")]
    pub timeout: Duration,
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;

    let log = transport.uart("console")?;

    let i2cs: Vec<_> = (0..3)
        .map(|idx| transport.i2c(idx.to_string().as_str()))
        .collect::<Result<_, _>>()?;

    // Wait for device to setup and signal ready
    _ = UartConsole::wait_for(&*log, "SYNC: Device Ready.*\n", opts.timeout)?;

    for i2c in &i2cs {
        const MEM_DEVICE_ADDR: u8 = 0x40_u8;

        // Arbitary address in the memory to write to
        const POINTER: u8 = 0x30_u8;

        const NUM_BYTES: usize = 16;
        let mut read_buf = [0u8; NUM_BYTES];

        let write_values: Vec<u8> = (0..NUM_BYTES as u8).collect();

        // Instead of one sequential write, split and write the values across two
        // transaction and write back to front, to demonstrate that the data is
        // written to the correct location based on the given pointer value

        const SPLIT: usize = NUM_BYTES / 2;

        let mut write_buf_first = vec![POINTER];
        write_buf_first.extend_from_slice(&write_values[..SPLIT]);

        let mut write_buf_second = vec![POINTER + SPLIT as u8];
        write_buf_second.extend_from_slice(&write_values[SPLIT..]);

        // First transaction: Write second part of data

        i2c.run_transaction(
            Some(MEM_DEVICE_ADDR),
            &mut [Transfer::Write(&write_buf_second)],
        )?;

        // Second transaction: Write first part of data, then repeated start to
        // reset pointer, then repeated start to read back all the written data

        i2c.run_transaction(
            Some(MEM_DEVICE_ADDR),
            &mut [
                Transfer::Write(&write_buf_first),
                Transfer::Write(&[POINTER]),
                Transfer::Read(&mut read_buf),
            ],
        )?;

        // Expect the read back data to match

        assert_eq!(&read_buf.as_slice(), &write_values.as_slice());
    }

    // Write magic value to second address, causing the test to exit successfully

    const MAGIC_DEVICE_ADDR: u8 = 0x41_u8;
    const MAGIC_VALUE: u8 = 0xAA_u8;

    i2cs[0].run_transaction(
        Some(MAGIC_DEVICE_ADDR),
        &mut [Transfer::Write(&[MAGIC_VALUE])],
    )?;

    let res = UartConsole::wait_for(&*log, "(PASS|FAIL)!.*\n", opts.timeout)?;
    match res[0].as_str() {
        x if x.starts_with("PASS!") => Ok(()),
        _ => Err(anyhow!("Failure result: {:?}", res)),
    }
}
