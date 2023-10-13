// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use clap::{Args, Parser};

use ft_lib::{run_sram_ft_provision, test_exit, test_unlock, ManufFtProvisioningActions};
use opentitanlib::dif::lc_ctrl::DifLcCtrlState;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::SramProgramParams;
use util_lib::hex_string_to_u32_arrayvec;

/// Provisioning data command-line parameters.
#[derive(Debug, Args, Clone)]
pub struct ManufFtProvisioningDataInput {
    /// TestUnlock token.
    #[arg(long, default_value = "0x11111111_11111111_11111111_11111111")]
    pub test_unlock_token: String,

    /// TestExit token.
    #[arg(long, default_value = "0x11111111_11111111_11111111_11111111")]
    pub test_exit_token: String,

    /// LC state to transition to from TEST_UNLOCKED*.
    #[arg(long, value_parser = DifLcCtrlState::parse_lc_state_str, default_value = "prod")]
    target_mission_mode_lc_state: DifLcCtrlState,
}

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    #[command(flatten)]
    provisioning_data: ManufFtProvisioningDataInput,

    #[command(flatten)]
    provisioning_actions: ManufFtProvisioningActions,

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
    let test_exit_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_exit_token.as_str())?;

    if opts.provisioning_actions.all_steps || opts.provisioning_actions.test_unlock {
        test_unlock(
            &transport,
            &opts.init.jtag_params,
            opts.init.bootstrap.options.reset_delay,
            &test_unlock_token,
        )?;
    }
    if opts.provisioning_actions.all_steps
        || opts.provisioning_actions.otp_creator_sw_cfg
        || opts.provisioning_actions.otp_owner_sw_cfg
        || opts.provisioning_actions.otp_hw_cfg
    {
        run_sram_ft_provision(
            &transport,
            &opts.init.jtag_params,
            opts.init.bootstrap.options.reset_delay,
            &opts.sram_program,
            &opts.provisioning_actions,
            opts.timeout,
        )?;
    }
    if opts.provisioning_actions.all_steps || opts.provisioning_actions.test_exit {
        test_exit(
            &transport,
            &opts.init.jtag_params,
            opts.init.bootstrap.options.reset_delay,
            &test_exit_token,
            opts.provisioning_data.target_mission_mode_lc_state,
        )?;
    }

    Ok(())
}
