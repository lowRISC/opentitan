// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};

use ot_hal::dif::rstmgr::{
    DifRstmgrResetInfo, RstmgrAlertInfoCtrl, RstmgrCpuInfoCtrl, RstmgrCpuRegwen, RstmgrReg,
};
use ot_hal::top::earlgrey as top_earlgrey;

use crate::app::TransportWrapper;
use crate::io::jtag::{JtagParams, JtagTap};

/// Reads out CPU crashdump info over JTAG.
///
/// Assumes we are already in a TEST_UNLOCKED* state, and TAP straps are cleared.
pub fn read_cpu_crashdump_data(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
) -> Result<()> {
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::RiscvTap)?;

    // Read out CPU crashdump info.
    let mut buf = [0u32];

    // Make sure that CPU_INFO is writable.
    jtag.read_memory32(
        top_earlgrey::RSTMGR_AON_BASE_ADDR as u32 + RstmgrReg::CpuRegwen as u32,
        &mut buf,
    )?;
    if buf[0] & RstmgrCpuRegwen::EN == 0 {
        bail!("CPU_REGWEN.EN is 0, cannot read CPU crash dump.");
    }

    let mut cpu_crashdump_info = [0u32; 16];
    jtag.read_memory32(
        top_earlgrey::RSTMGR_AON_BASE_ADDR as u32 + RstmgrReg::CpuInfoAttr as u32,
        &mut buf,
    )?;
    let len = buf[0];
    log::info!("CPU Crash Dump Info ({:?} words):", len);
    for i in 0..len {
        jtag.write_memory32(
            top_earlgrey::RSTMGR_AON_BASE_ADDR as u32 + RstmgrReg::CpuInfoCtrl as u32,
            &[RstmgrCpuInfoCtrl::INDEX.emplace(i) | RstmgrCpuInfoCtrl::EN],
        )?;
        jtag.read_memory32(
            top_earlgrey::RSTMGR_AON_BASE_ADDR as u32 + RstmgrReg::CpuInfo as u32,
            &mut buf,
        )?;
        cpu_crashdump_info[i as usize] = buf[0];
    }
    log::info!("  Current MTVAL         = 0x{:x?}", cpu_crashdump_info[0]);
    log::info!("  Current MPEC          = 0x{:x?}", cpu_crashdump_info[1]);
    log::info!("  Last Data Access Addr = 0x{:x?}", cpu_crashdump_info[2]);
    log::info!("  Next PC               = 0x{:x?}", cpu_crashdump_info[3]);
    log::info!("  PC                    = 0x{:x?}", cpu_crashdump_info[4]);
    log::info!("  Previous MTVAL        = 0x{:x?}", cpu_crashdump_info[5]);
    log::info!("  Previous MPEC         = 0x{:x?}", cpu_crashdump_info[6]);
    log::info!("  Double Fault          = 0x{:x?}", cpu_crashdump_info[7]);

    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;
    jtag.disconnect()?;

    Ok(())
}

/// Reads out alert crashdump info over JTAG.
///
/// Assumes we are already in a TEST_UNLOCKED* state, and TAP straps are cleared.
pub fn read_alert_crashdump_data(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
) -> Result<()> {
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::RiscvTap)?;

    let mut buf = [0u32];
    jtag.read_memory32(
        top_earlgrey::RSTMGR_AON_BASE_ADDR as u32 + RstmgrReg::AlertInfoAttr as u32,
        &mut buf,
    )?;
    let len = buf[0];
    log::info!("Alert Crash Dump Info ({:?} words):", len);
    for i in 0..len {
        jtag.write_memory32(
            top_earlgrey::RSTMGR_AON_BASE_ADDR as u32 + RstmgrReg::AlertInfoCtrl as u32,
            &[RstmgrAlertInfoCtrl::INDEX.emplace(i) | RstmgrAlertInfoCtrl::EN],
        )?;
        jtag.read_memory32(
            top_earlgrey::RSTMGR_AON_BASE_ADDR as u32 + RstmgrReg::AlertInfo as u32,
            &mut buf,
        )?;
        log::info!("  Word {:?} = 0x{:x?}", i, buf[0]);
    }

    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;
    jtag.disconnect()?;

    Ok(())
}

/// Reads out reset reason over JTAG.
///
/// Assumes we are already in a TEST_UNLOCKED* state, and TAP straps are cleared.
pub fn read_reset_reason(transport: &TransportWrapper, jtag_params: &JtagParams) -> Result<()> {
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::RiscvTap)?;

    let mut buf = [0u32];
    jtag.read_memory32(
        top_earlgrey::RSTMGR_AON_BASE_ADDR as u32 + RstmgrReg::ResetInfo as u32,
        &mut buf,
    )?;
    let reset_reason = buf[0];

    log::info!("Reset Reasons:");
    log::info!(
        "  PoR           = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::Por)) != 0
    );
    log::info!(
        "  LowPowerExit  = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::LowPowerExit)) != 0
    );
    log::info!(
        "  Sw            = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::Sw)) != 0
    );
    log::info!(
        "  HwReq         = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::HwReq)) != 0
    );
    log::info!(
        "  SysRstCtrl    = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::SysRstCtrl)) != 0
    );
    log::info!(
        "  Watchdog      = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::Watchdog)) != 0
    );
    log::info!(
        "  PowerUnstable = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::PowerUnstable)) != 0
    );
    log::info!(
        "  Escalation    = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::Escalation)) != 0
    );
    log::info!(
        "  Ndm           = {:?}",
        (reset_reason & u32::from(DifRstmgrResetInfo::Ndm)) != 0
    );

    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;
    jtag.disconnect()?;

    Ok(())
}
