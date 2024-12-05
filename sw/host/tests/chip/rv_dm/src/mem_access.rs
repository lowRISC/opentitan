// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::{ensure, Result};
use clap::Parser;
use rand::prelude::*;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::util::parse_int::ParseInt;

use bindgen::dif;
use top_earlgrey::top_earlgrey;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Path to the ROM binary.
    #[arg(long)]
    rom: PathBuf,

    #[arg(long)]
    rv_dm_delayed_enable: bool,

    /// Seed for random number generator.
    #[arg(long, value_parser = u64::from_str)]
    seed: Option<u64>,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "100s")]
    timeout: Duration,
}

const NUM_ACCESSES_PER_REGION: usize = 32;

// The last 32 bytes of ROM (ROM digest) are not accessible.
const ROM_ACCESSIBLE_BYTES: usize = top_earlgrey::ROM_SIZE_BYTES - 32;

fn test_mem_access(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let seed = opts.seed.unwrap_or_else(|| thread_rng().gen());
    log::info!("Random number generator seed is {:x}", seed);
    let mut rng = rand_chacha::ChaCha12Rng::seed_from_u64(seed);

    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let uart = &*transport.uart("console")?;
    uart.set_flow_control(true)?;

    log::info!("rv_dm_delayed_enable: {}", opts.rv_dm_delayed_enable);
    if opts.rv_dm_delayed_enable {
        UartConsole::wait_for(uart, r"DEBUG_MODE_ENABLED", opts.timeout)?;
    } else {
        // Avoid watchdog timeout by entering bootstrap mode.
        transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
        transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    }

    let jtag = &mut *opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    let rom_data = std::fs::read(&opts.rom)?;
    ensure!(rom_data.len() % 4 == 0);

    let rw_regions = [
        (
            "ram_ret",
            top_earlgrey::RAM_RET_AON_BASE_ADDR as u32,
            top_earlgrey::RAM_RET_AON_SIZE_BYTES as u32,
        ),
        (
            "ram_main",
            top_earlgrey::RAM_MAIN_BASE_ADDR as u32,
            top_earlgrey::RAM_MAIN_SIZE_BYTES as u32,
        ),
        (
            "otbn_imem",
            top_earlgrey::OTBN_BASE_ADDR as u32 + dif::OTBN_IMEM_REG_OFFSET,
            dif::OTBN_IMEM_SIZE_BYTES,
        ),
        (
            "otbn_dmem",
            top_earlgrey::OTBN_BASE_ADDR as u32 + dif::OTBN_DMEM_REG_OFFSET,
            dif::OTBN_DMEM_SIZE_BYTES,
        ),
    ];

    // Randomly generate accesses.
    let mut accesses = vec![];
    for (name, base, size) in rw_regions.iter().copied() {
        accesses.extend(
            (0..size)
                .step_by(4)
                .choose_multiple(&mut rng, NUM_ACCESSES_PER_REGION)
                .into_iter()
                .map(|offset| (name, base, offset, rng.gen::<u32>())),
        );
    }

    // Shuffle the accesses and perform write.
    accesses.shuffle(&mut rng);
    for (name, base, offset, value) in accesses.iter().copied() {
        log::info!("Writing to {name} (base {base:#x}) offset {offset:#x} with value {value:#x}");
        let addr = base + offset;
        jtag.write_memory32(addr, &[value])?;
    }

    // For ROM contents, instead of using random values, use the known value from ROM binary
    for offset in (0..ROM_ACCESSIBLE_BYTES as u32)
        .step_by(4)
        .choose_multiple(&mut rng, NUM_ACCESSES_PER_REGION)
    {
        accesses.push((
            "rom",
            top_earlgrey::ROM_BASE_ADDR as u32,
            offset,
            if offset as usize <= rom_data.len() {
                u32::from_le_bytes(rom_data[offset as usize..][..4].try_into().unwrap())
            } else {
                0
            },
        ));
    }

    // Shuffle the access again and confirm readback.
    accesses.shuffle(&mut rng);
    for (name, base, offset, value) in accesses {
        let addr = base + offset;
        let mut readback = 0;
        jtag.read_memory32(addr, std::slice::from_mut(&mut readback))?;
        log::info!("Reading from {name} (base {base:#x}) offset {offset:#x} with value {readback:#x} (expecting {value:#x})");
        ensure!(value == readback);
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_mem_access, &opts, &transport);

    Ok(())
}
