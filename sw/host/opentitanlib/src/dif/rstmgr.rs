// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

with_unknown! {
    pub enum DifRstmgrResetInfo : u32 {
        Por = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoPor as u32,
        LowPowerExit = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoLowPowerExit as u32,
        Sw = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoSw as u32,
        HwReq  = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoHwReq as u32,
        SysRstCtrl  = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoSysRstCtrl as u32,
        Watchdog  = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoWatchdog as u32,
        PowerUnstable = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoPowerUnstable as u32,
        Escalation = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoEscalation as u32,
        Ndm = bindgen::dif::dif_rstmgr_reset_info_kDifRstmgrResetInfoNdm as u32,
    }
}
