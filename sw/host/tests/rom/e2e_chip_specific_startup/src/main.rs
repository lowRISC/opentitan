// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::Result;
use clap::Parser;
use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boolean::MultiBitBool4;
use opentitanlib::dif::lc_ctrl::DifLcCtrlState;
use opentitanlib::execute_test;
use opentitanlib::test_utils::e2e_command::TestCommand;
use opentitanlib::test_utils::epmp::constants::*;
use opentitanlib::test_utils::epmp::{Epmp, EpmpAddressRange, EpmpEntry, EpmpRegionKind};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;
use std::time::Duration;

mod chip_specific_startup;
use chip_specific_startup::ChipStartup;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    /// OTP is unprogrammed; be permissive with OTP values.
    #[arg(long)]
    otp_unprogrammed: bool,
}

fn check_ast(opts: &Opts, cs: &ChipStartup) -> Result<()> {
    let en = MultiBitBool4::try_from(cs.otp.creator_sw_cfg_ast_init_en)?;
    log::info!("CREATOR_SW_CFG_AST_INIT_EN = {:#x}", en);
    // AST_INIT_EN should be either MultiBitBool4 True or False.  Other values are an error.
    match en {
        MultiBitBool4::True => assert_eq!(cs.ast_init_done, true),
        MultiBitBool4::False => assert_eq!(cs.ast_init_done, false),
        _ => {
            if opts.otp_unprogrammed {
                log::info!(
                    "CREATOR_SW_CFG_AST_INIT_EN is neither True nor False:  AST not checked."
                );
            } else {
                assert!(en.is_known_value());
            }
        }
    }
    Ok(())
}

fn check_jitter(opts: &Opts, cs: &ChipStartup) -> Result<()> {
    let en = MultiBitBool4::try_from(cs.otp.creator_sw_cfg_jitter_en)?;
    log::info!("CREATOR_SW_CFG_JITTER_EN = {:#x}", en);
    // Clock jitter should be disabled if JITTER_EN is MultiBitBool4 False. All other values
    // enable.
    match en {
        MultiBitBool4::False => assert_eq!(cs.jitter, false),
        MultiBitBool4::True => assert_eq!(cs.jitter, true),
        _ => {
            if opts.otp_unprogrammed {
                log::info!("CREATOR_SW_CFG_AST_JITTER_EN is neither True nor False:  Checking for jitter enabled.");
                assert_eq!(cs.jitter, true)
            } else {
                assert!(en.is_known_value());
            }
        }
    }
    Ok(())
}

fn check_entropy_config(_opts: &Opts, cs: &ChipStartup) -> Result<()> {
    let fips_enable = MultiBitBool4::try_from(cs.entropy.entropy_src & 0x0000_000F)?;
    let csrng_enable = MultiBitBool4::try_from(cs.entropy.csrng & 0x0000_000F)?;
    let edn_enable = MultiBitBool4::try_from(cs.entropy.edn & 0x0000_000F)?;
    let edn_boot_mode = MultiBitBool4::try_from((cs.entropy.edn >> 4) & 0x0000_000F)?;

    // No FIPS entropy for bootup.
    assert_eq!(fips_enable, MultiBitBool4::False);
    // CSRNG should be enabled.
    assert_eq!(csrng_enable, MultiBitBool4::True);
    // EDN should be enabled and in boot mode.
    assert_eq!(edn_enable, MultiBitBool4::True);
    assert_eq!(edn_boot_mode, MultiBitBool4::True);
    Ok(())
}

fn check_epmp(_opts: &Opts, cs: &ChipStartup) -> Result<()> {
    let lc_state = DifLcCtrlState(cs.lc_state);
    log::info!("lc_state = {:#x}", lc_state);
    let epmp = Epmp::from_raw_rv32(&cs.epmp.cfg, &cs.epmp.addr)?;
    log::info!("epmp = {:#x?}", epmp);

    // The hardware enables machine-mode-whitelist-policy and rule-locking-bypass at reset.
    assert_eq!(cs.epmp.mseccfg, EPMP_MSECCFG_MMWP | EPMP_MSECCFG_RLB);

    // Epmp entries not configured by the ROM. Some of these entries are unconfigured
    // because they're the lower half of a top-of-range entry.  They appear unconfigured here and
    // the range bounds are included in the `range` member of the TOR entry.
    assert!(matches!(
        epmp.entry[0],
        EpmpEntry {
            cfg: _,
            kind: EpmpRegionKind::Off,
            range: _
        }
    ));
    assert!(matches!(
        epmp.entry[3],
        EpmpEntry {
            cfg: _,
            kind: EpmpRegionKind::Off,
            range: _
        }
    ));
    assert!(matches!(
        epmp.entry[6],
        EpmpEntry {
            cfg: _,
            kind: EpmpRegionKind::Off,
            range: _
        }
    ));
    assert!(matches!(
        epmp.entry[7],
        EpmpEntry {
            cfg: _,
            kind: EpmpRegionKind::Off,
            range: _
        }
    ));
    assert!(matches!(
        epmp.entry[8],
        EpmpEntry {
            cfg: _,
            kind: EpmpRegionKind::Off,
            range: _
        }
    ));
    assert!(matches!(
        epmp.entry[9],
        EpmpEntry {
            cfg: _,
            kind: EpmpRegionKind::Off,
            range: _
        }
    ));
    assert!(matches!(
        epmp.entry[10],
        EpmpEntry {
            cfg: _,
            kind: EpmpRegionKind::Off,
            range: _
        }
    ));
    assert!(matches!(
        epmp.entry[12],
        EpmpEntry {
            cfg: _,
            kind: EpmpRegionKind::Off,
            range: _
        }
    ));

    // Epmp entries for ROM: .text, all of ROM, peripheral address space.
    assert!(matches!(
        epmp.entry[1],
        EpmpEntry {
            cfg: EPMP_CFG_LRX,
            kind: EpmpRegionKind::Tor,
            range: EpmpAddressRange(0x8000, _)
        }
    ));
    assert!(matches!(
        epmp.entry[2],
        EpmpEntry {
            cfg: EPMP_CFG_LRO,
            kind: EpmpRegionKind::Napot,
            range: EpmpAddressRange(0x8000, 0x10000)
        }
    ));
    assert!(matches!(
        epmp.entry[11],
        EpmpEntry {
            cfg: EPMP_CFG_LRW,
            kind: EpmpRegionKind::Tor,
            range: EpmpAddressRange(0x4000_0000, 0x5000_0000)
        }
    ));

    // Epmp regions for RAM: a stack guard and all of RAM.
    assert!(matches!(
        epmp.entry[14],
        EpmpEntry {
            cfg: EPMP_CFG_LOCKED_NONE,
            kind: EpmpRegionKind::Na4,
            range: EpmpAddressRange(0x1001_c000, 0x1001_c004)
        }
    ));
    assert!(matches!(
        epmp.entry[15],
        EpmpEntry {
            cfg: EPMP_CFG_LRW,
            kind: EpmpRegionKind::Napot,
            range: EpmpAddressRange(0x1000_0000, 0x1002_0000)
        }
    ));

    // Flash execution: mapped by ROM when choosing a ROM_EXT.
    assert!(matches!(
        epmp.entry[4],
        EpmpEntry {
            cfg: EPMP_CFG_LRX,
            kind: EpmpRegionKind::Tor,
            range: EpmpAddressRange(0x2000_0400, _)
        }
    ));
    assert!(matches!(
        epmp.entry[5],
        EpmpEntry {
            cfg: EPMP_CFG_LRO,
            kind: EpmpRegionKind::Napot,
            range: EpmpAddressRange(0x2000_0000, 0x2010_0000)
        }
    ));
    // Debug: only enabled for Test, Dev and RMA states:
    match lc_state {
        DifLcCtrlState::TestUnlocked0
        | DifLcCtrlState::TestUnlocked1
        | DifLcCtrlState::TestUnlocked2
        | DifLcCtrlState::TestUnlocked3
        | DifLcCtrlState::TestUnlocked4
        | DifLcCtrlState::TestUnlocked5
        | DifLcCtrlState::TestUnlocked6
        | DifLcCtrlState::TestUnlocked7
        | DifLcCtrlState::Dev
        | DifLcCtrlState::Rma => {
            log::info!(
                "Checking that the debug memory region is enabled in state {:#x}",
                lc_state
            );
            assert!(matches!(
                epmp.entry[13],
                EpmpEntry {
                    cfg: EPMP_CFG_LRWX,
                    kind: EpmpRegionKind::Napot,
                    range: EpmpAddressRange(0x10000, 0x11000)
                }
            ));
        }
        _ => {
            log::info!(
                "Checking that the debug memory region is disabled in state {:#x}",
                lc_state
            );
            assert!(matches!(
                epmp.entry[13],
                EpmpEntry {
                    cfg: EPMP_CFG_LOCKED_NONE,
                    kind: EpmpRegionKind::Napot,
                    range: EpmpAddressRange(0x10000, 0x11000)
                }
            ));
        }
    }
    Ok(())
}

fn check_interrupts(_opts: &Opts, cs: &ChipStartup) -> Result<()> {
    // According to "The RISC-V Instruction Set Manual Volume II: Privileged Architecture Version
    // 1.9.1", section 3.1.7 Figure 3.6, the interrupt
    // enable bits for each privilege mode are all packed into the
    // low nybble of the `mstatus` register.
    //
    // We only would ever expect to see MIE (b3) set, but we check that
    // all of the eneable bits are clear.
    //
    // https://www2.eecs.berkeley.edu/Pubs/TechRpts/2016/EECS-2016-161.html
    let mstatus = cs.mstatus & 0x0000_000F;
    assert_eq!(mstatus, 0);
    Ok(())
}

fn check_sram(_opts: &Opts, cs: &ChipStartup) -> Result<()> {
    let lc_state = DifLcCtrlState(cs.lc_state);
    log::info!("lc_state = {:#x}", lc_state);
    assert!(cs.sram.scr_key_valid);
    match lc_state {
        DifLcCtrlState::TestUnlocked0
        | DifLcCtrlState::Dev
        | DifLcCtrlState::Prod
        | DifLcCtrlState::ProdEnd
        | DifLcCtrlState::Rma => {
            log::info!(
                "Checking that the SRAM scrambling key seed is valid in LC state {:#x}",
                lc_state
            );
            assert!(cs.sram.scr_key_seed_valid);
        }
        _ => {
            log::info!(
                "Checking that the SRAM scrambling key seed is not valid in LC state {:#x}",
                lc_state
            );
            assert!(!cs.sram.scr_key_seed_valid);
        }
    }
    assert!(cs.sram.init_done);
    Ok(())
}

fn test_chip_specific_startup(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("console")?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    TestCommand::ChipStartup.send(&*uart)?;
    let response = ChipStartup::recv(&*uart, opts.timeout, false)?;
    log::info!("{:#x?}", response);

    check_ast(opts, &response)?;
    check_jitter(opts, &response)?;
    check_entropy_config(opts, &response)?;
    check_epmp(opts, &response)?;
    check_interrupts(opts, &response)?;
    check_sram(opts, &response)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_chip_specific_startup, &opts, &transport);
    Ok(())
}
