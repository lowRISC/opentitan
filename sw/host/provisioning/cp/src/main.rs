// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use clap::Parser;

use cp_lib::{reset_and_lock, run_sram_cp_provision, ManufCpProvisioningDataInput};
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::dif::lc_ctrl::DifLcCtrlState;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc::read_lc_state;
use opentitanlib::test_utils::load_sram_program::SramProgramParams;
use ujson_lib::provisioning_data::ManufCpProvisioningData;
use util_lib::{hash_lc_token, hex_string_to_u32_arrayvec};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    #[command(flatten)]
    provisioning_data: ManufCpProvisioningDataInput,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "BOOTSTRAP")]
    console_spi: String,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    let spi = transport.spi(&opts.console_spi)?;
    let spi_console_device = SpiConsoleDevice::new(&*spi)?;

    let provisioning_data = ManufCpProvisioningData {
        device_id: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.device_id.as_str())?,
        manuf_state: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.manuf_state.as_str())?,
        wafer_auth_secret: hex_string_to_u32_arrayvec::<8>(
            opts.provisioning_data.wafer_auth_secret.as_str(),
        )?,
        test_unlock_token_hash: hash_lc_token(opts.provisioning_data.test_unlock_token.as_bytes())?,
        test_exit_token_hash: hash_lc_token(opts.provisioning_data.test_exit_token.as_bytes())?,
    };

    // Only run CP provisioning if requested in any of the TestUnlocked states, except the last
    // state (TestUnlocked7), as this state requires special handling of the wafer authentication
    // secret, which is not yet implemented.
    let lc_state = read_lc_state(
        &transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
    )?;
    match lc_state {
        DifLcCtrlState::TestUnlocked0
        | DifLcCtrlState::TestUnlocked1
        | DifLcCtrlState::TestUnlocked2
        | DifLcCtrlState::TestUnlocked3
        | DifLcCtrlState::TestUnlocked4
        | DifLcCtrlState::TestUnlocked5
        | DifLcCtrlState::TestUnlocked6 => {
            run_sram_cp_provision(
                &transport,
                &opts.init.jtag_params,
                opts.init.bootstrap.options.reset_delay,
                &opts.sram_program,
                &provisioning_data,
                &spi_console_device,
                opts.timeout,
            )?;
            // Only perform lock if we are in TEST_UNLOCKED0, otherwise we are running from a later
            // stage and want to run FT stage directly after.
            if lc_state == DifLcCtrlState::TestUnlocked0 {
                reset_and_lock(
                    &transport,
                    &opts.init.jtag_params,
                    opts.init.bootstrap.options.reset_delay,
                )?;
            } else {
                log::info!("Skipping resetting and locking the device.");
            }
        }
        _ => {
            log::info!("Skipping executing the SRAM CP provisioning binary.");
        }
    };

    Ok(())
}
