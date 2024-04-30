// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::Result;
use clap::Parser;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

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
    #[arg(long, help = "Next Owner private key (ECDSA P256)")]
    next_owner_key: PathBuf,
    #[arg(long, help = "Next Owner activate private key (ECDSA P256)")]
    next_activate_key: PathBuf,
    #[arg(long, help = "Next Owner unlock private key (ECDSA P256)")]
    next_unlock_key: PathBuf,
    #[arg(long, help = "Next Owner's application public key (RSA3K)")]
    next_application_key: PathBuf,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    let uart = transport.uart("console")?;
    let rescue = RescueSerial::new(Rc::clone(&uart));

    let data = transfer_lib::get_boot_log(&transport, &rescue)?;
    transfer_lib::ownership_unlock_any(&transport, &rescue, data.rom_ext_nonce, &opts.unlock_key)?;

    transfer_lib::create_owner(
        &transport,
        &rescue,
        &opts.next_owner_key,
        &opts.next_activate_key,
        &opts.next_unlock_key,
        &opts.next_application_key,
    )?;

    // At this point, the device should be unlocked and should have accepted the owner
    // configuration.  Owner code should run and report the state as `UANY`.
    transport.reset_target(Duration::from_millis(50), /*clear_uart=*/ true)?;
    let capture = UartConsole::wait_for(
        &*uart,
        r"(?msR)ownership_state = UANY$.*ownership_transfers = (\d+)$.*PASS!$",
        opts.timeout,
    )?;
    let transfers0 = capture[1].parse::<u32>()?;

    let data = transfer_lib::get_boot_log(&transport, &rescue)?;
    transfer_lib::ownership_activate(
        &transport,
        &rescue,
        data.rom_ext_nonce,
        &opts.next_activate_key,
    )?;

    // After the activate command, the device should report the ownership state as `OWND`.
    transport.reset_target(Duration::from_millis(50), /*clear_uart=*/ true)?;
    let capture = UartConsole::wait_for(
        &*uart,
        r"(?msR)ownership_state = OWND$.*ownership_transfers = (\d+)$.*PASS!$",
        opts.timeout,
    )?;
    let transfers1 = capture[1].parse::<u32>()?;
    assert_eq!(transfers0 + 1, transfers1);
    Ok(())
}
