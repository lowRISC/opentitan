// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use regex::Regex;
use structopt::StructOpt;
use std::thread;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boolean::MultiBitBool8;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{JtagParams, JtagTap, RiscvCsr, RiscvGpr, RiscvReg};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

use top_earlgrey::top_earlgrey_memory;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,
    #[structopt(flatten)]
    jtag: JtagParams,
}

fn reset(transport: &TransportWrapper, strappings: &[&str], reset_delay: Duration) -> Result<()> {
    log::info!("Resetting target...");
    for strapping in strappings.iter() {
        transport.pin_strapping(strapping)?.apply()?;
    }
    transport.reset_target(reset_delay, true)?;
    // we want to hold the strapping configuration here because in some life cycle states,
    // the tap multiplexing is dynamic so remove the tap strap would actually change the tap
    Ok(())
}

fn stress_openocd(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // repeat the same test 50 times (stay below timeout)
    log::info!("Reset chip");
    reset(
        transport,
        &["PINMUX_TAP_RISCV"],
        opts.init.bootstrap.options.reset_delay,
    )?;
    let jtag = transport.jtag(&opts.jtag)?;
    log::info!("Connect to RISC-V");
    jtag.connect(JtagTap::RiscvTap)?;
    jtag.halt()?;
    // write the whole SRAM
    let base = top_earlgrey_memory::TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR as u32;
    let size = top_earlgrey_memory::TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES;
    let data : Vec<u32> = (0..(size / 4)).map(|x| x as u32).collect();
    log::info!("Write the whole SRAM");
    jtag.write_memory32(base, &data)?;
    // read it back
    let mut data2 = vec![0u32; size / 4];
    log::info!("Read back SRAM");
    jtag.read_memory32(base, &mut data2)?;

    jtag.disconnect()?;
    Ok(())
}


fn test_openocd(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Reset the device
    let uart = transport.uart("console")?;

    reset(transport, &[], opts.init.bootstrap.options.reset_delay)?;
    const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);

    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(Regex::new(r"PASS!")?),
        ..Default::default()
    };
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    log::info!("result: {:?}", result);

    //
    // Test the RISC-V TAP
    //
    reset(
        transport,
        &["PINMUX_TAP_RISCV"],
        opts.init.bootstrap.options.reset_delay,
    )?;

    let jtag = transport.jtag(&opts.jtag)?;
    jtag.connect(JtagTap::RiscvTap)?;
    jtag.reset(false)?;
    // Definitions for hardware registers
    let lc_ctrl_base_addr = top_earlgrey_memory::TOP_EARLGREY_LC_CTRL_BASE_ADDR as u32;
    let lc_ctrl_transition_if_addr = lc_ctrl_base_addr + LcCtrlReg::ClaimTransitionIf.byte_offset();
    let lc_ctrl_state_addr = lc_ctrl_base_addr + LcCtrlReg::LcState.byte_offset();
    let lc_ctrl_transition_regwen_addr =
        lc_ctrl_base_addr + LcCtrlReg::TransitionRegwen.byte_offset();
    log::info!(
        "LC_CTRL_TRANSITION_IF_ADDR = {:x}",
        lc_ctrl_transition_if_addr
    );
    log::info!("LC_CTRL_STATE_ADDR = {:x}", lc_ctrl_state_addr);
    log::info!(
        "LC_CTRL_TRANSITION_REGWEN_ADDR = {:x}",
        lc_ctrl_transition_regwen_addr
    );
    // Test reads by checking the LC_STATE register
    let mut lc_ctrl_state = [0u32; 1];
    assert_eq!(
        jtag.read_memory32(lc_ctrl_state_addr, &mut lc_ctrl_state)?,
        1
    );
    assert_eq!(
        lc_ctrl_state[0],
        DifLcCtrlState::TestUnlocked0.redundant_encoding()
    );
    // Test writes by trying to claim the transitions mutex
    let mut lc_ctrl_transition_regwen = [0u32; 1];
    assert_eq!(
        jtag.read_memory32(
            lc_ctrl_transition_regwen_addr,
            &mut lc_ctrl_transition_regwen
        )?,
        1
    );
    assert_eq!(lc_ctrl_transition_regwen[0], 0);
    let mut lc_ctrl_transition_if = [u8::from(MultiBitBool8::True) as u32; 1];

    jtag.write_memory32(lc_ctrl_transition_if_addr, &lc_ctrl_transition_if)?;
    assert_eq!(
        jtag.read_memory32(
            lc_ctrl_transition_regwen_addr,
            &mut lc_ctrl_transition_regwen
        )?,
        1
    );
    assert_eq!(lc_ctrl_transition_regwen[0], 1);
    // Release mutex
    lc_ctrl_transition_if[0] = u8::from(MultiBitBool8::False) as u32;
    jtag.write_memory32(lc_ctrl_transition_if_addr, &lc_ctrl_transition_if)?;
    assert_eq!(
        jtag.read_memory32(
            lc_ctrl_transition_regwen_addr,
            &mut lc_ctrl_transition_regwen
        )?,
        1
    );
    assert_eq!(lc_ctrl_transition_regwen[0], 0);

    // Test bulk read/writes by reading the content of the RAM, then overwrite it with
    // known values and try to read-back, we restore the content afterwards
    let test_ram_addr = top_earlgrey_memory::TOP_EARLGREY_RAM_RET_AON_BASE_ADDR as u32;
    const SIZE: usize = 20;
    let mut ram = [0u8; SIZE];
    assert_eq!(jtag.read_memory(test_ram_addr, &mut ram)?, SIZE);
    log::info!("ram: {:?}", ram);
    let test_data = (0..SIZE as u8).collect::<Vec<u8>>();
    jtag.write_memory(test_ram_addr, &test_data)?;
    let mut test_data2 = [0u8; SIZE];
    assert_eq!(jtag.read_memory(test_ram_addr, &mut test_data2)?, SIZE);
    log::info!("ram: {:?}", test_data2);
    assert_eq!(test_data, test_data2);
    // restore RAM
    jtag.write_memory(test_ram_addr, &ram)?;

    //
    // Test register read/writes
    //
    let orig_sp = jtag.read_riscv_reg(&RiscvReg::GprByName(RiscvGpr::SP))?;
    log::info!("SP: {:x}", orig_sp);
    let orig_pc = jtag.read_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::DPC))?;
    log::info!("PC: {:x}", orig_pc);
    jtag.write_riscv_reg(&RiscvReg::GprByName(RiscvGpr::SP), 0xdeadbeef)?;
    jtag.write_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::DPC), 0xcc00ffee)?;
    log::info!(
        "SP: {:x}",
        jtag.read_riscv_reg(&RiscvReg::GprByName(RiscvGpr::SP))?
    );
    log::info!(
        "PC: {:x}",
        jtag.read_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::DPC))?
    );
    // restore
    jtag.write_riscv_reg(&RiscvReg::GprByName(RiscvGpr::SP), orig_sp)?;
    jtag.write_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::DPC), orig_pc)?;

    //
    // Test reset
    //
    jtag.reset(/* run */ false)?;
    // the reset address is 0x8080
    assert_eq!(
        jtag.read_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::DPC))?,
        0x8080
    );
    jtag.step()?;
    // the first instruction is a jump to 0x8180
    assert_eq!(
        jtag.read_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::DPC))?,
        0x8180
    );
    jtag.reset(/* run */ true)?;
    jtag.halt()?;
    // at this point the target must have execute at least one instruction so it should
    // not be at the reset vector anymore
    assert_ne!(
        jtag.read_riscv_reg(&RiscvReg::CsrByName(RiscvCsr::DPC))?,
        0x8080
    );
    jtag.resume()?;

    jtag.disconnect()?;

    //
    // Test the LC TAP
    //
    reset(
        transport,
        &["PINMUX_TAP_LC"],
        opts.init.bootstrap.options.reset_delay,
    )?;

    let jtag = transport.jtag(&opts.jtag)?;
    jtag.connect(JtagTap::LcTap)?;

    // Test reads by checking the LC_STATE register
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        DifLcCtrlState::TestUnlocked0.redundant_encoding()
    );

    // Test writes by trying to claim the transitions mutex
    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionRegwen)?, 0x00);
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::ClaimTransitionIf,
        u8::from(MultiBitBool8::True) as u32,
    )?;
    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionRegwen)?, 0x01);
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::ClaimTransitionIf,
        u8::from(MultiBitBool8::False) as u32,
    )?;
    jtag.disconnect()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_openocd, &opts, &transport);
    execute_test!(stress_openocd, &opts, &transport);

    Ok(())
}
