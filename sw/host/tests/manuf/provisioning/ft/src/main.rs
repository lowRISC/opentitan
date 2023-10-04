// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use clap::{Args, Parser};

use cp_lib::hex_string_to_u32_arrayvec;
use ft_lib::{run_sram_ft_provision, test_unlock};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::SramProgramParams;

/// Provisioning data command-line parameters.
#[derive(Debug, Args, Clone)]
pub struct ManufFtProvisioningDataInput {
    /// TestUnlock token to provision.
    #[arg(long, default_value = "0x11111111_11111111_11111111_11111111")]
    pub test_unlock_token: String,

    /// TestExit token to provision.
    #[arg(long, default_value = "0x11111111_11111111_11111111_11111111")]
    pub test_exit_token: String,
}

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    #[command(flatten)]
    provisioning_data: ManufFtProvisioningDataInput,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let test_unlock_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_unlock_token.as_str())?;

    test_unlock(
        &transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
        &test_unlock_token,
    )?;
    run_sram_ft_provision(
        &transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
        &opts.sram_program,
        opts.timeout,
    )?;

    Ok(())
}
