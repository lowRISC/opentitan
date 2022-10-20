// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

with_unknown! {
    pub enum DifLcCtrlState: u32 {
        Raw = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateRaw as u32,
        TestUnlocked0 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked0 as u32,
        TestLocked0 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked0 as u32,
        TestUnlocked1 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked1 as u32,
        TestLocked1 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked1 as u32,
        TestUnlocked2 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked2 as u32,
        TestLocked2 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked2 as u32,
        TestUnlocked3 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked3 as u32,
        TestLocked3 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked3 as u32,
        TestUnlocked4 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked4 as u32,
        TestLocked4 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked4 as u32,
        TestUnlocked5 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked5 as u32,
        TestLocked5 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked5 as u32,
        TestUnlocked6 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked6 as u32,
        TestLocked6 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked6 as u32,
        TestUnlocked7 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked7 as u32,
        Dev = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateDev as u32,
        Prod = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateProd as u32,
        ProdEnd = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateProdEnd as u32,
        Rma = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateRma as u32,
        Scrap = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateScrap as u32,
        PostTransition = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStatePostTransition as u32,
        Escalate = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateEscalate as u32,
        StateInvalide = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateInvalid as u32,
    }
}
