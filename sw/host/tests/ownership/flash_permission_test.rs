// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Result, anyhow};
use clap::Parser;
use regex::Regex;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::{TransportWrapper, UartRx};
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
    #[arg(long, help = "Next Owner's application public key (ECDSA P256)")]
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
    #[arg(long, default_value = "SlotA", help = "Which slot to rescue into")]
    rescue_slot: BootSlot,
    #[arg(
        long,
        default_value = "SlotA",
        help = "Which slot the ROM_EXT is expected to execute from"
    )]
    expected_rom_ext_slot: BootSlot,

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

fn flash_info_check(info: &[FlashRegion<'_>], unlocked: bool) -> Result<()> {
    // Flash info regions when no OwnerReserved pages are configured:
    let config = [
        FlashRegion("info", 0, 0, 0, "uu-uu-uu-uu-uu-uu", "LK"), // factory ID
        FlashRegion("info", 0, 0, 1, "uu-uu-uu-uu-uu-uu", "LK"), // creator secret
        FlashRegion("info", 0, 0, 2, "uu-uu-uu-uu-uu-uu", "LK"), // owner secret
        FlashRegion("info", 0, 0, 3, "uu-uu-uu-uu-uu-uu", "LK"), // wafer auth secret
        FlashRegion("info", 0, 0, 4, "RD-xx-xx-SC-EC-xx", "LK"), // attestation key seeds
        FlashRegion("info", 0, 0, 5, "xx-xx-xx-xx-xx-xx", "UN"), // owner reserved
        FlashRegion("info", 0, 0, 6, "xx-xx-xx-xx-xx-xx", "UN"), // owner reserved
        FlashRegion("info", 0, 0, 7, "xx-xx-xx-xx-xx-xx", "UN"), // owner reserved
        FlashRegion("info", 0, 0, 8, "xx-xx-xx-xx-xx-xx", "UN"), // owner reserved
        FlashRegion("info", 0, 0, 9, "RD-xx-xx-SC-EC-xx", "LK"), // factory certs
        FlashRegion("info", 1, 0, 0, "uu-uu-uu-uu-uu-uu", "LK"), // boot data 0
        FlashRegion("info", 1, 0, 1, "uu-uu-uu-uu-uu-uu", "LK"), // boot data 1
        FlashRegion("info", 1, 0, 2, "RD-xx-xx-SC-EC-xx", "LK"), // owner config 0
        if unlocked {
            FlashRegion("info", 1, 0, 3, "RD-WR-ER-SC-EC-xx", "LK") // owner config 1
        } else {
            FlashRegion("info", 1, 0, 3, "RD-xx-xx-SC-EC-xx", "LK") // owner config 1
        },
        FlashRegion("info", 1, 0, 4, "uu-uu-uu-uu-uu-uu", "LK"), // creator reserved
        FlashRegion("info", 1, 0, 5, "RD-WR-ER-xx-xx-HE", "UN"), // owner reserved
        FlashRegion("info", 1, 0, 6, "xx-xx-xx-xx-xx-xx", "UN"), // owner reserved
        FlashRegion("info", 1, 0, 7, "xx-xx-xx-xx-xx-xx", "UN"), // owner reserved
        FlashRegion("info", 1, 0, 8, "xx-xx-xx-xx-xx-xx", "UN"), // owner reserved
        FlashRegion("info", 1, 0, 9, "RD-xx-xx-SC-EC-xx", "LK"), // dice certs
    ];
    assert_eq!(info.len(), config.len());
    let mut err = 0;
    for i in 0..config.len() {
        if info[i] != config[i] {
            log::error!("INFO entry {i}: {:?} != {:?}", info[i], config[i]);
            err += 1;
        }
    }
    if err != 0 {
        Err(anyhow!("INFO lockdown mismatch"))
    } else {
        Ok(())
    }
}

fn flash_permission_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let rescue = RescueSerial::new(uart.clone());

    log::info!("###### Get Boot Log (1/2) ######");
    let (data, devid) = transfer_lib::get_device_info(transport, &rescue)?;
    log::info!("###### Ownership Unlock ######");
    transfer_lib::ownership_unlock(
        transport,
        &rescue,
        opts.unlock_mode,
        data.rom_ext_nonce,
        devid.din,
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

    // The expected_rom_ext_slot is where we expect the ROM_EXT to execute.
    let romext_region = match opts.expected_rom_ext_slot {
        BootSlot::SlotA => ["RD-xx-xx-uu-uu-uu", "RD-WR-ER-uu-uu-uu"],
        BootSlot::SlotB => ["RD-WR-ER-uu-uu-uu", "RD-xx-xx-uu-uu-uu"],
        _ => return Err(anyhow!("Unknown boot slot {}", data.bl0_slot)),
    };

    if opts.dual_owner_boot_check {
        log::info!("###### Boot in Dual-Owner Mode ######");
        // At this point, the device should be unlocked and should have accepted the owner
        // configuration.  Owner code should run and report the ownership state.
        //
        // The flash configuration will be the previous owner in Side A and
        // the new owner in SideB.
        transport.reset_with_delay(UartRx::Clear, Duration::from_millis(50))?;
        let capture = UartConsole::wait_for_bytes(
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
        // Note: The number of regions and indices of the regions is currently
        // Earlgrey-specific.
        //
        // Note: when in an unlocked state, flash lockdown doesn't apply, so neither
        // the `protect_when_active` nor `lock` bits for individual regions will
        // affect the region config.

        // The ROM_EXT always protects itself in regions 0 and 1.
        assert_eq!(
            region[0],
            FlashRegion("data", 0, 0, 32, romext_region[0], "LK")
        );
        assert_eq!(
            region[1],
            FlashRegion("data", 1, 256, 32, romext_region[1], "LK")
        );
        assert_eq!(
            region[2],
            FlashRegion("data", 2, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
        );
        assert_eq!(
            region[3],
            FlashRegion("data", 3, 0, 0, "xx-xx-xx-xx-xx-xx", "UN")
        );
        // Flash SideB is the next owner configuration.
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

        flash_info_check(&region[8..], /*unlocked=*/ true)?;
    }

    log::info!("###### Get Boot Log (2/2) ######");
    let (data, _) = transfer_lib::get_device_info(transport, &rescue)?;

    log::info!("###### Ownership Activate Block ######");
    transfer_lib::ownership_activate(
        transport,
        &rescue,
        data.rom_ext_nonce,
        devid.din,
        opts.activate_key
            .as_deref()
            .unwrap_or(&opts.next_activate_key),
    )?;

    if let Some(fw) = &opts.rescue_after_activate {
        let data = std::fs::read(fw)?;
        rescue.enter(transport, /*reset_target=*/ true)?;
        rescue.wait()?;
        rescue.update_firmware(opts.rescue_slot, &data)?;
        // Clear the opposite slot because we changed the scrambling/ecc settings
        // for the application area of flash.
        rescue.update_firmware(opts.rescue_slot.opposite()?, &[0xFFu8])?;
        rescue.reboot()?;
    }

    log::info!("###### Boot After Transfer Complete ######");
    // After the activate command, the device should report the ownership state as `OWND`.
    transport.reset_with_delay(UartRx::Clear, Duration::from_millis(50))?;
    let capture = UartConsole::wait_for_bytes(
        &*uart,
        r"(?msR)Running(.*)Finished.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;
    if capture[0].starts_with("BFV") {
        return RomError(u32::from_str_radix(&capture[2], 16)?).into();
    }
    let region = FlashRegion::find_all(&capture[1])?;

    // The rescue_slot should be the active side and has protect_when_active = true.
    let app_region = match opts.rescue_slot {
        BootSlot::SlotA => ["RD-xx-xx-SC-EC-xx", "RD-WR-ER-SC-EC-xx"],
        BootSlot::SlotB => ["RD-WR-ER-SC-EC-xx", "RD-xx-xx-SC-EC-xx"],
        _ => return Err(anyhow!("Unknown boot slot {}", data.bl0_slot)),
    };

    //
    // Since we are in a locked ownership state, we expect the region configuration
    // to reflect both the `protect_when_active` and `lock` properties of the
    // owner's flash configuration.
    let locked = if opts.config_kind.is_flash_locked() {
        "LK"
    } else {
        "UN"
    };
    // The ROM_EXT always protects itself in regions 0 and 1.
    assert_eq!(
        region[0],
        FlashRegion("data", 0, 0, 32, romext_region[0], "LK")
    );
    assert_eq!(
        region[1],
        FlashRegion("data", 1, 256, 32, romext_region[1], "LK")
    );
    // Flash Slot A:
    assert_eq!(
        region[2],
        FlashRegion("data", 2, 32, 192, app_region[0], locked)
    );
    assert_eq!(
        region[3],
        FlashRegion("data", 3, 224, 32, "RD-WR-ER-xx-xx-HE", locked)
    );
    // Flash Slot B:
    assert_eq!(
        region[4],
        FlashRegion("data", 4, 288, 192, app_region[1], locked)
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

    flash_info_check(&region[8..], /*unlocked=*/ false)?;
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
