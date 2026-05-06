// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Result, ensure};
use clap::Parser;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use opentitanlib::app::{TransportWrapper, UartRx};
use opentitanlib::io::uart::Uart;
use opentitanlib::chip::rom_error::RomError;
use opentitanlib::ownership::{OwnershipKeyAlg, MinSecurityVersion, OwnershipUpdateMode};
use opentitanlib::rescue::serial::RescueSerial;
use opentitanlib::rescue::{EntryMode, Rescue};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;
use transfer_lib::HybridPair;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
    #[arg(long, default_value_t = OwnershipKeyAlg::EcdsaP256, help = "Current Owner key algorithm")]
    next_key_alg: OwnershipKeyAlg,
    #[arg(long, help = "Next Owner private key (ECDSA P256)")]
    next_owner_key: Option<PathBuf>,
    #[arg(long, help = "Next Owner activate private key (ECDSA P256)")]
    next_activate_key: Option<PathBuf>,
    #[arg(long, help = "Next Owner unlock private key (ECDSA P256)")]
    next_unlock_key: Option<PathBuf>,
    #[arg(long, help = "Next Owner's application public key (ECDSA P256)")]
    next_application_key: PathBuf,

    #[arg(long, help = "Next Owner private key (SPX)")]
    next_owner_key_spx: Option<PathBuf>,
    #[arg(long, help = "Next Owner activate private key (SPX)")]
    next_activate_key_spx: Option<PathBuf>,
    #[arg(long, help = "Next Owner unlock private key (SPX)")]
    next_unlock_key_spx: Option<PathBuf>,

    #[arg(long, value_parser = humantime::parse_duration, help = "Max timeout to enter rescue mode")]
    rescue_enter_delay: Option<Duration>,

    #[arg(
        long,
        value_enum,
        default_value = "basic",
        help = "Style of Owner Config for this test"
    )]
    config_kind: transfer_lib::OwnerConfigKind,
}

fn wait_for_boot(uart: &dyn Uart, timeout: Duration, expected_ver: u32, expected_min: u32) -> Result<()> {
    let capture = UartConsole::wait_for(
        uart,
        r"(?msR)Running.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
        timeout,
    )?;
    if capture[0].starts_with("BFV") {
        let err = u32::from_str_radix(&capture[1], 16)?;
        if err == 0 {
            log::info!("Detected expected write-and-reboot (BFV:00000000). Waiting for next boot...");
            // Wait again for the actual boot to PASS!
            let capture2 = UartConsole::wait_for(
                uart,
                r"(?msR)Running.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
                timeout,
            )?;
            if capture2[0].starts_with("BFV") {
                return RomError(u32::from_str_radix(&capture2[1], 16)?).into();
            }
            ensure!(capture2[0].contains(&format!("config_version = {expected_ver}")), "Expected config_version = {expected_ver}");
            ensure!(capture2[0].contains(&format!("bl0_min_sec_ver = {expected_min}")), "Expected bl0_min_sec_ver = {expected_min}");
        } else {
            return RomError(err).into();
        }
    } else {
        ensure!(capture[0].contains(&format!("config_version = {expected_ver}")), "Expected config_version = {expected_ver}");
        ensure!(capture[0].contains(&format!("bl0_min_sec_ver = {expected_min}")), "Expected bl0_min_sec_ver = {expected_min}");
    }
    Ok(())
}

fn bl0_secver_persistence_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let rescue = RescueSerial::new(Rc::clone(&uart), opts.rescue_enter_delay);

    log::info!("###### Get Device Info (1) ######");
    rescue.enter(transport, EntryMode::Reset)?;
    let (data, _devid) = transfer_lib::get_device_info(transport, &rescue)?;

    log::info!("###### Upload Owner Block V2 (min_sec_ver = 5) ######");
    transfer_lib::create_owner(
        transport,
        &rescue,
        data.rom_ext_nonce,
        opts.next_key_alg,
        HybridPair::load(
            opts.next_owner_key.as_deref(),
            opts.next_owner_key_spx.as_deref(),
        )?,
        HybridPair::load(
            opts.next_activate_key.as_deref(),
            opts.next_activate_key_spx.as_deref(),
        )?,
        HybridPair::load(
            opts.next_unlock_key.as_deref(),
            opts.next_unlock_key_spx.as_deref(),
        )?,
        &opts.next_application_key,
        opts.config_kind,
        |owner| {
            owner.config_version = 2;
            owner.min_security_version_bl0 = MinSecurityVersion(5);
            owner.update_mode = OwnershipUpdateMode::NewVersion;
        },
    )?;

    log::info!("###### Boot After V2 Update (should trigger reboot and persist) ######");
    transport.reset_with_delay(UartRx::Clear, Duration::from_millis(50))?;
    wait_for_boot(&*uart, opts.timeout, 2, 5)?;

    log::info!("###### Reboot again to verify persistence ######");
    transport.reset_with_delay(UartRx::Clear, Duration::from_millis(50))?;

    let capture = UartConsole::wait_for(
        &*uart,
        r"(?msR)Running.*PASS!$|BFV:([0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;
    ensure!(!capture[0].starts_with("BFV"), "Boot failed or triggered unexpected reboot");
    ensure!(capture[0].contains("config_version = 2"), "Expected config_version = 2");
    ensure!(capture[0].contains("bl0_min_sec_ver = 5"), "Expected bl0_min_sec_ver = 5");

    log::info!("###### BL0 SecVer Persistence test passed! ######");
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    bl0_secver_persistence_test(&opts, &transport)
}
