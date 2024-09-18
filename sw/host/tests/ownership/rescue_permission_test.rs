// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{anyhow, Result};
use clap::Parser;
use regex::Regex;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boot_svc::{BootSlot, UnlockMode};
use opentitanlib::rescue::serial::RescueSerial;
use opentitanlib::test_utils::init::InitializeTest;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
    #[arg(long, help = "Unlock private key (ECDSA P256)")]
    unlock_key: PathBuf,
    #[arg(long, help = "Activate private key (ECDSA P256)")]
    activate_key: Option<PathBuf>,
    #[arg(long, help = "Next Owner private key (ECDSA P256)")]
    next_owner_key: PathBuf,
    #[arg(long, help = "Next Owner public key (ECDSA P256)")]
    next_owner_key_pub: Option<PathBuf>,
    #[arg(long, help = "Next Owner activate private key (ECDSA P256)")]
    next_activate_key: PathBuf,
    #[arg(long, help = "Next Owner unlock private key (ECDSA P256)")]
    next_unlock_key: PathBuf,
    #[arg(long, help = "Next Owner's application public key (RSA3K)")]
    next_application_key: PathBuf,

    #[arg(
        long,
        value_enum,
        default_value = "with-rescue-restricted",
        help = "Style of Owner Config for this test"
    )]
    config_kind: transfer_lib::OwnerConfigKind,

    #[arg(long, default_value = "Any", help = "Mode of the unlock operation")]
    unlock_mode: UnlockMode,
    #[arg(long, help = "Expected error condition")]
    expected_error: Option<String>,
}

fn rescue_permission_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let rescue = RescueSerial::new(Rc::clone(&uart));

    log::info!("###### Get Boot Log (1/2) ######");
    let data = transfer_lib::get_boot_log(transport, &rescue)?;
    log::info!("###### Ownership Unlock ######");
    transfer_lib::ownership_unlock(
        transport,
        &rescue,
        opts.unlock_mode,
        data.rom_ext_nonce,
        &opts.unlock_key,
        if opts.unlock_mode == UnlockMode::Endorsed {
            opts.next_owner_key_pub.as_deref()
        } else {
            None
        },
    )?;

    log::info!("###### Upload Owner Block ######");
    transfer_lib::create_owner(
        transport,
        &rescue,
        &opts.next_owner_key,
        &opts.next_activate_key,
        &opts.next_unlock_key,
        &opts.next_application_key,
        opts.config_kind,
        /*customize=*/ |_| {},
    )?;

    log::info!("###### Get Boot Log (2/2) ######");
    let data = transfer_lib::get_boot_log(transport, &rescue)?;

    log::info!("###### Ownership Activate Block ######");
    transfer_lib::ownership_activate(
        transport,
        &rescue,
        data.rom_ext_nonce,
        opts.activate_key
            .as_deref()
            .unwrap_or(&opts.next_activate_key),
    )?;

    log::info!("###### Check Rescue Dis-Allowed Command ######");
    // We'll check a boot_svc command that has been removed from the
    // allowlist when we use the `WithRescueRestricted` configuration.
    rescue.enter(transport, /*reset_target=*/ true)?;
    let result = rescue.set_next_bl0_slot(
        /*primary=*/ BootSlot::Unspecified,
        /*next=*/ BootSlot::SlotA,
    );

    let result = result.unwrap_err().to_string();
    log::info!("Expecting 'Cancelled' in response to a dis-allowed command");
    log::info!("set_next_bl0_slot(primary=Unspecified, next=SlotA) -> {result}");
    assert_eq!(result, "Cancelled");
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let result = rescue_permission_test(&opts, &transport);
    if let Some(error) = &opts.expected_error {
        match result {
            Ok(_) => Err(anyhow!("Ok when expecting {error:?}")),
            Err(e) => {
                let re = Regex::new(error).expect("regex");
                if re.is_match(&e.to_string()) {
                    log::info!("Got expected error code: {e}");
                    Ok(())
                } else {
                    Err(anyhow!("Expected {error:?} but got {e}"))
                }
            }
        }
    } else {
        result
    }
}
