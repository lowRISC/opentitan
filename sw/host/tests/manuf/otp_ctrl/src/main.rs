// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This test performs a OTP writes/locks over JTAG to confirm this method of OTP memory
//! programming is functional.

use anyhow::Context;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::otp_ctrl::{DaiParam, Partition};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::otp_ctrl::{OtpParam, OtpPartition};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;

    execute_test!(program_readback, &opts, &transport);
    execute_test!(lock_partition, &opts, &transport);

    Ok(())
}

/// Program an OTP parameter and read it back to confirm the write.
fn program_readback(opts: &Opts, transport: &TransportWrapper) -> anyhow::Result<()> {
    // Set the TAP straps for the CPU and reset.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .apply()
        .context("failed to apply RISCV TAP strapping")?;
    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset")?;

    // Connect to the RISCV TAP via JTAG.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)
        .context("failed to connect to RISCV TAP over JTAG")?;

    // Program and then read back `MANUF_STATE`.
    let write_data = [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF];
    OtpParam::write_param(&mut *jtag, DaiParam::ManufState, &write_data)
        .context("failed to write MANUF_STATE")?;

    let mut read_data = [0xff; 8];
    OtpParam::read_param(&mut *jtag, DaiParam::ManufState, &mut read_data)
        .context("failed to read MANUF_STATE")?;

    assert_eq!(read_data, write_data);

    jtag.disconnect()?;

    Ok(())
}

/// Lock a partition and check its digest.
fn lock_partition(opts: &Opts, transport: &TransportWrapper) -> anyhow::Result<()> {
    // Set the TAP straps for the CPU and reset.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .apply()
        .context("failed to apply RISCV TAP strapping")?;
    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset")?;

    // Connect to the RISCV TAP via JTAG.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)
        .context("failed to connect to RISCV TAP over JTAG")?;

    // Read the HW_CFG partition's digest, which should be 0 (unlocked):
    let digest = OtpPartition::read_digest(&mut *jtag, Partition::HW_CFG)
        .context("failed to read HW_CFG partition's digest")?;

    assert_eq!(digest, [0x00; 2]);

    // Lock the partition.
    OtpPartition::lock(&mut *jtag, Partition::HW_CFG).context("failed to lock HW_CFG partition")?;

    // Read the digest again to see if it's been calculated (locked):
    let digest = OtpPartition::read_digest(&mut *jtag, Partition::HW_CFG)
        .context("failed to read HW_CFG partition's digest")?;

    assert_ne!(digest, [0x00; 2]);

    jtag.disconnect()?;

    Ok(())
}
