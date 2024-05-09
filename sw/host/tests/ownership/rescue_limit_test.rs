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
        default_value = "with-rescue",
        help = "Style of Owner Config for this test"
    )]
    config_kind: transfer_lib::OwnerConfigKind,

    #[arg(
        long,
        help = "Load a firmware payload via rescue after activating ownership"
    )]
    rescue_after_activate: Option<PathBuf>,

    #[arg(long, default_value = "Any", help = "Mode of the unlock operation")]
    unlock_mode: UnlockMode,
    #[arg(long, help = "Expected error condition")]
    expected_error: Option<String>,
}

fn flash_limit_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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

    log::info!("###### Rescue Payload of Zeros ######");
    // We send a 448K payload of all zeros.  The rescue config sets the size
    // limit of the firmware section to 384K, so we expect to get a "Cancel"
    // from the target.
    //
    // We should get the cancellation at XModem-1K block 386 because the rescue
    // protocol buffers 2K blocks to write to flash.  After writing the first
    // 384K, block 385 and 386 will be buffered in RAM and the rescue module
    // will reject the write request and terminate the upload.
    let data = vec![0u8; 448 * 1024];
    rescue.enter(transport, /*reset_target=*/ true)?;
    let result = rescue.update_firmware(BootSlot::SlotA, &data);
    assert_eq!(result.unwrap_err().to_string(), "Cancelled");
    log::info!("Got expected 'Cancel' during upload of too-large payload.");

    log::info!("###### Boot After Transfer Complete ######");
    log::info!("Expecting to see 0 before offset 0x70000 and 0xffffffff at/after offset 0x70000.");
    // The firmware in the target will print the first word of each flash page
    // in the range [0x10000..0x80000).  We'll capture the last word of the
    // firmware segment and the first word of the filesystem segment and
    // verify that the firmware segement is programmed (value 0) and the
    // filesystem segment remains unprogramed (value ffffffff).
    transport.reset_target(Duration::from_millis(50), /*clear_uart=*/ true)?;
    let capture = UartConsole::wait_for(
        &*uart,
        r"(?msR)flash 0x2006f800 = (\w+)$.*flash 0x20070000 = (\w+)$.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;

    if capture[0].starts_with("BFV") {
        return RomError(u32::from_str_radix(&capture[3], 16)?).into();
    }
    assert_eq!(capture[1], "0");
    assert_eq!(capture[2], "ffffffff");
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let result = flash_limit_test(&opts, &transport);
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
