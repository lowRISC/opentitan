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
        default_value = "with-flash-locked",
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

#[derive(Debug, PartialEq, Eq)]
struct FlashRegion<'a>(&'a str, u32, u32, u32, &'a str, &'a str);

impl FlashRegion<'_> {
    // Parse the text from the firmware into a list of FlashRegions.
    fn find_all(v: &str) -> Result<Vec<FlashRegion<'_>>> {
        let mut result = Vec::new();
        let re = Regex::new(
            // Matches strings of the following forms:
            // data region n=0 st=0 sz=32 RD-xx-xx-xx-xx-xx UN
            // info region bank=0 part=0 page=6 xx-xx-xx-xx-xx-xx UN
            r"(?msR)(?<type>\w+) region (?:(?:n=(?<n>\d+) st=(?<st>\d+) sz=(?<sz>\d+))|(?:bank=(?<bank>\d+) part=(?<part>\d+) page=(?<page>\d+))) (?<perm>[^ ]+) (?<lock>\w+)$"
        ).unwrap();
        for cap in re.captures_iter(v) {
            if &cap["type"] == "data" {
                result.push(FlashRegion(
                    cap.name("type").unwrap().as_str(),
                    cap["n"].parse()?,
                    cap["st"].parse()?,
                    cap["sz"].parse()?,
                    cap.name("perm").unwrap().as_str(),
                    cap.name("lock").unwrap().as_str(),
                ));
            } else if &cap["type"] == "info" {
                result.push(FlashRegion(
                    cap.name("type").unwrap().as_str(),
                    cap["bank"].parse()?,
                    cap["part"].parse()?,
                    cap["page"].parse()?,
                    cap.name("perm").unwrap().as_str(),
                    cap.name("lock").unwrap().as_str(),
                ));
            } else {
                return Err(anyhow!("Unknown flash region type: {:?}", &cap["type"]));
            }
        }
        Ok(result)
    }
}

fn flash_permission_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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

    if opts.dual_owner_boot_check {
        log::info!("###### Boot in Dual-Owner Mode ######");
        // At this point, the device should be unlocked and should have accepted the owner
        // configuration.  Owner code should run and report the ownership state.
        //
        // The flash configuration will be the previous owner in Side A and
        // the new owner in SideB.
        transport.reset_target(Duration::from_millis(50), /*clear_uart=*/ true)?;
        let capture = UartConsole::wait_for(
            &*uart,
            r"(?msR)Running(.*)Finished.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
            opts.timeout,
        )?;
        if capture[0].starts_with("BFV") {
            return RomError(u32::from_str_radix(&capture[2], 16)?).into();
        }
        let region = FlashRegion::find_all(&capture[1])?;
        // Flash SideA is the previous owner configuration.  The `fake` test owner
        // has no flash configuration at all.
        //
        // Note: when in an unlocked state, flash lockdown doesn't apply, so neither
        // the `protect_when_primary` nor `lock` bits for individual regions will
        // affect the region config.
        assert_eq!(
            region[0],
            FlashRegion("data", 0, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
        );
        assert_eq!(
            region[1],
            FlashRegion("data", 1, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
        );
        assert_eq!(
            region[2],
            FlashRegion("data", 2, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
        );
        // Flash SideB is the next owner configuration.
        assert_eq!(
            region[3],
            FlashRegion("data", 3, 256, 32, "RD-WR-ER-xx-xx-xx", "UN")
        );
        assert_eq!(
            region[4],
            FlashRegion("data", 4, 288, 192, "RD-WR-ER-SC-EC-xx", "UN")
        );
        assert_eq!(
            region[5],
            FlashRegion("data", 5, 480, 32, "RD-WR-ER-xx-xx-HE", "UN")
        );
        assert_eq!(
            region[6],
            FlashRegion("data", 6, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
        );
        assert_eq!(
            region[7],
            FlashRegion("data", 7, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
        );
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
        r"(?msR)Running(.*)Finished.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;
    if capture[0].starts_with("BFV") {
        return RomError(u32::from_str_radix(&capture[3], 16)?).into();
    }
    let region = FlashRegion::find_all(&capture[1])?;
    // Flash SideA is the primary side and has protect_when_primary = true.
    //
    // Since we are in a locked ownership state, we expect the region configuration
    // to reflect both the `protect_when_primary` and `lock` properties of the
    // owner's flash configuration.
    let locked = if opts.config_kind.is_flash_locked() {
        "LK"
    } else {
        "UN"
    };
    assert_eq!(
        region[0],
        FlashRegion("data", 0, 0, 32, "RD-xx-xx-xx-xx-xx", locked)
    );
    assert_eq!(
        region[1],
        FlashRegion("data", 1, 32, 192, "RD-xx-xx-SC-EC-xx", locked)
    );
    assert_eq!(
        region[2],
        FlashRegion("data", 2, 224, 32, "RD-WR-ER-xx-xx-HE", locked)
    );
    // Flash SideB is the secondary side, so protect_when_primary doesn't apply.
    assert_eq!(
        region[3],
        FlashRegion("data", 3, 256, 32, "RD-WR-ER-xx-xx-xx", locked)
    );
    assert_eq!(
        region[4],
        FlashRegion("data", 4, 288, 192, "RD-WR-ER-SC-EC-xx", locked)
    );
    assert_eq!(
        region[5],
        FlashRegion("data", 5, 480, 32, "RD-WR-ER-xx-xx-HE", locked)
    );
    // Regions 6 and 7 aren't specified in the owner config and therefore
    // should be left unlocked.
    assert_eq!(
        region[6],
        FlashRegion("data", 6, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
    );
    assert_eq!(
        region[7],
        FlashRegion("data", 7, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
    );

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let result = flash_permission_test(&opts, &transport);
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
