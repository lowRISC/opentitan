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
        default_value = "basic",
        help = "Style of Owner Config for this test"
    )]
    config_kind: transfer_lib::OwnerConfigKind,

    #[arg(
        long,
        help = "Load a firmware payload via rescue after activating ownership"
    )]
    rescue_after_activate: Option<PathBuf>,

    #[arg(long, default_value_t = true, action = clap::ArgAction::Set, help = "Check the firmware boot in dual-owner mode")]
    dual_owner_boot_check: bool,

    #[arg(long, default_value = "Any", help = "Mode of the unlock operation")]
    unlock_mode: UnlockMode,
    #[arg(long, help = "Expected error condition")]
    expected_error: Option<String>,
}

fn transfer_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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
    )?;

    let mut transfers0 = 0;
    if opts.dual_owner_boot_check {
        log::info!("###### Boot in Dual-Owner Mode ######");
        // At this point, the device should be unlocked and should have accepted the owner
        // configuration.  Owner code should run and report the ownership state.
        transport.reset_target(Duration::from_millis(50), /*clear_uart=*/ true)?;
        let capture = UartConsole::wait_for(
            &*uart,
            r"(?msR)ownership_state = (\w+)$.*ownership_transfers = (\d+)$.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
            opts.timeout,
        )?;
        if capture[0].starts_with("BFV") {
            return RomError(u32::from_str_radix(&capture[3], 16)?).into();
        }
        match opts.unlock_mode {
            UnlockMode::Any => assert_eq!(capture[1], "UANY"),
            UnlockMode::Endorsed => assert_eq!(capture[1], "UEND"),
            UnlockMode::Update => assert_eq!(capture[1], "USLF"),
            _ => return Err(anyhow!("Unexpected ownership state: {}", capture[1])),
        }
        transfers0 = capture[2].parse::<u32>()?;
    }

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

    if let Some(fw) = &opts.rescue_after_activate {
        let data = std::fs::read(fw)?;
        rescue.enter(transport, /*reset_target=*/ true)?;
        rescue.update_firmware(BootSlot::SlotA, &data)?;
    }

    log::info!("###### Boot After Transfer Complete ######");
    // After the activate command, the device should report the ownership state as `OWND`.
    transport.reset_target(Duration::from_millis(50), /*clear_uart=*/ true)?;
    let capture = UartConsole::wait_for(
        &*uart,
        r"(?msR)ownership_state = (\w+)$.*ownership_transfers = (\d+)$.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;
    if capture[0].starts_with("BFV") {
        return RomError(u32::from_str_radix(&capture[3], 16)?).into();
    }
    assert_eq!(capture[1], "OWND");
    let transfers1 = capture[2].parse::<u32>()?;
    assert_eq!(transfers0 + 1, transfers1);
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let result = transfer_test(&opts, &transport);
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
