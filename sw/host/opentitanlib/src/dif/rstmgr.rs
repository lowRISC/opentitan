// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

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
