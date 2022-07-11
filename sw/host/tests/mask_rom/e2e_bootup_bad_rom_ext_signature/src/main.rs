// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use regex::Regex;
use std::io::Write;
use std::path::PathBuf;
use std::time::Duration;
use structopt::StructOpt;
use tempfile::NamedTempFile;

mod helpers;
use helpers::init::InitializeTest;
use opentitanlib::app::TransportWrapper;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "5s",
        help = "ROM_EXT boot detection timeout",
    )]
    timeout: Duration,

    #[structopt(long, help = "ROM_EXT image")]
    rom_ext: PathBuf,
}

fn corrupt_rom_ext(rom_ext_path: &PathBuf) -> Result<NamedTempFile> {
    // Read image file
    let mut buffer = match std::fs::read(&rom_ext_path) {
        Ok(file) => file,
        Err(error) => panic!("Problem reading the file: {:?}", error),
    };

    // Flip a bit within the signature field of the ROM_EXT manifest
    buffer[80] = &buffer[80] ^ 0b10;

    // Write the file back out
    let mut corrupted_rom_ext = NamedTempFile::new()?;
    corrupted_rom_ext.write_all(&buffer)?;

    Ok(corrupted_rom_ext)
}

fn test_corrupted_rom_ext(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let corrupted_rom_ext = corrupt_rom_ext(&opts.rom_ext)?;
    println!("Corrupted rom ext: {:?}", corrupted_rom_ext);

    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("0")?;
    // This is a negative test, so a boot failure is expected
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"BFV:[0-9a-z]{8}\r\nLCV:[0-9a-z]{8}\r\n")?),
        exit_failure: Some(Regex::new(r"PASS!")?),
        ..Default::default()
    };

    // Reuse the alread-configured `Bootstrap` to load the corrupted ROM_EXT.
    opts.init
        .bootstrap
        .load(transport, corrupted_rom_ext.path())?;

    // Now watch the console for the exit conditions.
    let mut stdout = std::io::stdout();
    let result = console.interact(&*uart, None, Some(&mut stdout))?;
    match result {
        ExitStatus::ExitSuccess => {}
        _ => {
            bail!("FAIL: {:?}", result);
        }
    };
    corrupted_rom_ext.close()?; // explicitly close the tempfile
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    test_corrupted_rom_ext(&opts, &transport)?;
    Ok(())
}
