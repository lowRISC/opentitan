// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
#[non_exhaustive]
pub enum RstmgrReg {
    AlertTest = bindgen::dif::RSTMGR_ALERT_TEST_REG_OFFSET,
    ResetReq = bindgen::dif::RSTMGR_RESET_REQ_REG_OFFSET,
    ResetInfo = bindgen::dif::RSTMGR_RESET_INFO_REG_OFFSET,
    AlertRegwen = bindgen::dif::RSTMGR_ALERT_REGWEN_REG_OFFSET,
    AlertInfoCtrl = bindgen::dif::RSTMGR_ALERT_INFO_CTRL_REG_OFFSET,
    AlertInfoAttr = bindgen::dif::RSTMGR_ALERT_INFO_ATTR_REG_OFFSET,
    AlertInfo = bindgen::dif::RSTMGR_ALERT_INFO_REG_OFFSET,
    CpuRegwen = bindgen::dif::RSTMGR_CPU_REGWEN_REG_OFFSET,
    CpuInfoCtrl = bindgen::dif::RSTMGR_CPU_INFO_CTRL_REG_OFFSET,
    CpuInfoAttr = bindgen::dif::RSTMGR_CPU_INFO_ATTR_REG_OFFSET,
    CpuInfo = bindgen::dif::RSTMGR_CPU_INFO_REG_OFFSET,
    SwRstRegwen0 = bindgen::dif::RSTMGR_SW_RST_REGWEN_0_REG_OFFSET,
    SwRstRegwen1 = bindgen::dif::RSTMGR_SW_RST_REGWEN_1_REG_OFFSET,
    SwRstCtrlN0 = bindgen::dif::RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET,
    SwRstCtrlN1 = bindgen::dif::RSTMGR_SW_RST_CTRL_N_1_REG_OFFSET,
    ErrCode = bindgen::dif::RSTMGR_ERR_CODE_REG_OFFSET,
}

with_unknown! {
    pub enum DifRstmgrResetInfo: u32 {
        Por = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoPor,
        LowPowerExit = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoLowPowerExit,
        Sw = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoSw,
        HwReq  = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoHwReq,
        SysRstCtrl  = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoSysRstCtrl,
        Watchdog  = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoWatchdog,
        PowerUnstable = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoPowerUnstable,
        Escalation = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoEscalation,
        Ndm = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoNdm,
    }
}
