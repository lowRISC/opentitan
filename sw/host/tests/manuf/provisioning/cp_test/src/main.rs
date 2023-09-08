// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;

use cp_lib::{
    hex_string_to_u32_arrayvec, reset_and_lock, run_sram_cp_provision, unlock_raw,
    ManufCpProvisioningData, Opts,
};
use opentitanlib::app::TransportWrapper;

fn cp_provision(
    opts: &Opts,
    transport: &TransportWrapper,
    provisioning_data: &ManufCpProvisioningData,
) -> Result<()> {
    unlock_raw(opts, transport)?;
    run_sram_cp_provision(opts, transport, provisioning_data)?;
    reset_and_lock(opts, transport)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let provisioning_data = ManufCpProvisioningData {
        device_id: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.device_id.as_str())?,
        manuf_state: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.manuf_state.as_str())?,
        wafer_auth_secret: hex_string_to_u32_arrayvec::<8>(
            opts.provisioning_data.wafer_auth_secret.as_str(),
        )?,
        test_unlock_token: hex_string_to_u32_arrayvec::<4>(
            opts.provisioning_data.test_unlock_token.as_str(),
        )?,
        test_exit_token: hex_string_to_u32_arrayvec::<4>(
            opts.provisioning_data.test_exit_token.as_str(),
        )?,
    };

    cp_provision(&opts, &transport, &provisioning_data)?;

    // TODO(#19573): transition to PROD.
    // TODO(#19573): bootstrap flash binary to check OTP / flash info fields provisioned during CP.

    Ok(())
}
