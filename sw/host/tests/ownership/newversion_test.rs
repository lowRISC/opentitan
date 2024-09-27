// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{anyhow, ensure, Result};
use clap::Parser;
use regex::Regex;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::rom_error::RomError;
use opentitanlib::rescue::serial::RescueSerial;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
    #[arg(long, help = "Next Owner private key (ECDSA P256)")]
    next_owner_key: PathBuf,
    #[arg(long, help = "Next Owner public key (ECDSA P256)")]
    next_owner_key_pub: Option<PathBuf>,
    #[arg(long, help = "Next Owner activate private key (ECDSA P256)")]
    next_activate_key: PathBuf,
    #[arg(long, help = "Next Owner unlock private key (ECDSA P256)")]
    next_unlock_key: PathBuf,
    #[arg(long, help = "Next Owner's application public key (ECDSA P256)")]
    next_application_key: PathBuf,
    #[arg(
        long,
        default_value_t = transfer_lib::TEST_OWNER_CONFIG_VERSION,
        help = "Configuration version to put in the owner config"
    )]
    config_version: u32,

    #[arg(
        long,
        value_enum,
        default_value = "basic",
        help = "Style of Owner Config for this test"
    )]
    config_kind: transfer_lib::OwnerConfigKind,

    #[arg(long, help = "Expected success conditions")]
    expect: Vec<String>,

    #[arg(long, help = "Expected error condition")]
    expected_error: Option<String>,
}

fn newversion_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let rescue = RescueSerial::new(Rc::clone(&uart));

    log::info!("###### Upload Owner Block ######");
    transfer_lib::create_owner(
        transport,
        &rescue,
        &opts.next_owner_key,
        &opts.next_activate_key,
        &opts.next_unlock_key,
        &opts.next_application_key,
        opts.config_kind,
        /*customize=*/
        |owner| {
            owner.config_version = opts.config_version;
        },
    )?;

    log::info!("###### Boot After Update Complete ######");
    transport.reset_target(Duration::from_millis(50), /*clear_uart=*/ true)?;
    let capture = UartConsole::wait_for(
        &*uart,
        r"(?msR)Running.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;
    if capture[0].starts_with("BFV") {
        return RomError(u32::from_str_radix(&capture[1], 16)?).into();
    }

    for exp in opts.expect.iter() {
        let erx = Regex::new(exp)?;
        ensure!(erx.is_match(&capture[0]), "Did not find expected output {exp:?}");
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let result = newversion_test(&opts, &transport);
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
