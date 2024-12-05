// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use bitflags::bitflags;
use num_enum::IntoPrimitive;
use serde::{Deserialize, Serialize};

use crate::with_unknown;

with_unknown! {
    pub enum DifLcCtrlState: u32 {
        Raw = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateRaw ,
        TestUnlocked0 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked0 ,
        TestLocked0 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked0 ,
        TestUnlocked1 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked1 ,
        TestLocked1 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked1 ,
        TestUnlocked2 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked2 ,
        TestLocked2 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked2 ,
        TestUnlocked3 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked3 ,
        TestLocked3 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked3 ,
        TestUnlocked4 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked4 ,
        TestLocked4 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked4 ,
        TestUnlocked5 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked5 ,
        TestLocked5 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked5 ,
        TestUnlocked6 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked6 ,
        TestLocked6 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestLocked6 ,
        TestUnlocked7 = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateTestUnlocked7 ,
        Dev = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateDev ,
        Prod = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateProd ,
        ProdEnd = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateProdEnd ,
        Rma = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateRma ,
        Scrap = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateScrap ,
        PostTransition = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStatePostTransition ,
        Escalate = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateEscalate ,
        StateInvalid = bindgen::dif::dif_lc_ctrl_state_kDifLcCtrlStateInvalid ,
    }
}

pub struct DifLcCtrlTransCheck {
    /// Whether the transition is valid.
    pub valid: bool,
    /// Whether the transition requires a token.
    pub token: bool,
}

impl DifLcCtrlState {
    pub fn from_redundant_encoding(encoding: u32) -> Result<Self> {
        let base_encoding = encoding & 0x1fu32;
        if base_encoding > u32::from(DifLcCtrlState::StateInvalid) {
            bail!("Invalid life cycle state value.");
        }
        Ok(DifLcCtrlState(encoding & 0x1fu32))
    }

    /// Encode the given life cycle state in a redundant format where the
    /// five-bit value is repeated six times.
    pub fn redundant_encoding(&self) -> u32 {
        let value: u32 = self.0;
        assert_eq!(value & 0b11111, value);
        (0..6).fold(0u32, |acc, _| (acc << 5) | value)
    }

    pub fn lc_state_to_str(self) -> &'static str {
        match self {
            DifLcCtrlState::Raw => "raw",
            DifLcCtrlState::TestUnlocked0 => "test_unlocked0",
            DifLcCtrlState::TestLocked0 => "test_locked0",
            DifLcCtrlState::TestUnlocked1 => "test_unlocked1",
            DifLcCtrlState::TestLocked1 => "test_locked1",
            DifLcCtrlState::TestUnlocked2 => "test_unlocked2",
            DifLcCtrlState::TestLocked2 => "test_locked2",
            DifLcCtrlState::TestUnlocked3 => "test_unlocked3",
            DifLcCtrlState::TestLocked3 => "test_locked3",
            DifLcCtrlState::TestUnlocked4 => "test_unlocked4",
            DifLcCtrlState::TestLocked4 => "test_locked4",
            DifLcCtrlState::TestUnlocked5 => "test_unlocked5",
            DifLcCtrlState::TestLocked5 => "test_locked5",
            DifLcCtrlState::TestUnlocked6 => "test_unlocked6",
            DifLcCtrlState::TestLocked6 => "test_locked6",
            DifLcCtrlState::TestUnlocked7 => "test_unlocked7",
            DifLcCtrlState::Dev => "dev",
            DifLcCtrlState::Prod => "prod",
            DifLcCtrlState::ProdEnd => "prod_end",
            DifLcCtrlState::Rma => "rma",
            DifLcCtrlState::Scrap => "scrap",
            DifLcCtrlState::PostTransition => "post_transition",
            DifLcCtrlState::Escalate => "escalate",
            _ => "invalid",
        }
    }

    pub fn parse_lc_state_str(lc_state_str: &str) -> Result<Self> {
        match lc_state_str {
            "raw" => Ok(DifLcCtrlState::Raw),
            "test_unlocked0" => Ok(DifLcCtrlState::TestUnlocked0),
            "test_locked0" => Ok(DifLcCtrlState::TestLocked0),
            "test_unlocked1" => Ok(DifLcCtrlState::TestUnlocked1),
            "test_locked1" => Ok(DifLcCtrlState::TestLocked1),
            "test_unlocked2" => Ok(DifLcCtrlState::TestUnlocked2),
            "test_locked2" => Ok(DifLcCtrlState::TestLocked2),
            "test_unlocked3" => Ok(DifLcCtrlState::TestUnlocked3),
            "test_locked3" => Ok(DifLcCtrlState::TestLocked3),
            "test_unlocked4" => Ok(DifLcCtrlState::TestUnlocked4),
            "test_locked4" => Ok(DifLcCtrlState::TestLocked4),
            "test_unlocked5" => Ok(DifLcCtrlState::TestUnlocked5),
            "test_locked5" => Ok(DifLcCtrlState::TestLocked5),
            "test_unlocked6" => Ok(DifLcCtrlState::TestUnlocked6),
            "test_locked6" => Ok(DifLcCtrlState::TestLocked6),
            "test_unlocked7" => Ok(DifLcCtrlState::TestUnlocked7),
            "dev" => Ok(DifLcCtrlState::Dev),
            "prod" => Ok(DifLcCtrlState::Prod),
            "prod_end" => Ok(DifLcCtrlState::ProdEnd),
            "rma" => Ok(DifLcCtrlState::Rma),
            "scrap" => Ok(DifLcCtrlState::Scrap),
            "post_transition" => Ok(DifLcCtrlState::PostTransition),
            "escalate" => Ok(DifLcCtrlState::Escalate),
            _ => Ok(DifLcCtrlState::StateInvalid),
        }
    }

    /// Checks whether a transition is valid and whether a non-zero token is
    /// required.
    pub fn check_transition(self, target: DifLcCtrlState) -> DifLcCtrlTransCheck {
        match (self, target) {
            // Transitions that require a token.
            (DifLcCtrlState::Raw, DifLcCtrlState::TestUnlocked0)
            | (DifLcCtrlState::Raw, DifLcCtrlState::TestUnlocked1)
            | (DifLcCtrlState::Raw, DifLcCtrlState::TestUnlocked2)
            | (DifLcCtrlState::Raw, DifLcCtrlState::TestUnlocked3)
            | (DifLcCtrlState::Raw, DifLcCtrlState::TestUnlocked4)
            | (DifLcCtrlState::Raw, DifLcCtrlState::TestUnlocked5)
            | (DifLcCtrlState::Raw, DifLcCtrlState::TestUnlocked6)
            | (DifLcCtrlState::Raw, DifLcCtrlState::TestUnlocked7)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestUnlocked4, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestUnlocked4, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestUnlocked4, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestUnlocked5, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestUnlocked5, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestUnlocked5, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestUnlocked6, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestUnlocked6, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestUnlocked6, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestUnlocked7, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestUnlocked7, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestUnlocked7, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::TestUnlocked1)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::TestUnlocked2)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::TestUnlocked3)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::TestUnlocked4)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::TestUnlocked5)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::TestUnlocked6)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::TestUnlocked7)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::TestUnlocked2)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::TestUnlocked3)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::TestUnlocked4)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::TestUnlocked5)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::TestUnlocked6)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::TestUnlocked7)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::TestUnlocked3)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::TestUnlocked4)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::TestUnlocked5)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::TestUnlocked6)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::TestUnlocked7)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestLocked3, DifLcCtrlState::TestUnlocked4)
            | (DifLcCtrlState::TestLocked3, DifLcCtrlState::TestUnlocked5)
            | (DifLcCtrlState::TestLocked3, DifLcCtrlState::TestUnlocked6)
            | (DifLcCtrlState::TestLocked3, DifLcCtrlState::TestUnlocked7)
            | (DifLcCtrlState::TestLocked3, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestLocked3, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestLocked3, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestLocked4, DifLcCtrlState::TestUnlocked5)
            | (DifLcCtrlState::TestLocked4, DifLcCtrlState::TestUnlocked6)
            | (DifLcCtrlState::TestLocked4, DifLcCtrlState::TestUnlocked7)
            | (DifLcCtrlState::TestLocked4, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestLocked4, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestLocked4, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestLocked5, DifLcCtrlState::TestUnlocked6)
            | (DifLcCtrlState::TestLocked5, DifLcCtrlState::TestUnlocked7)
            | (DifLcCtrlState::TestLocked5, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestLocked5, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestLocked5, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::TestLocked6, DifLcCtrlState::TestUnlocked7)
            | (DifLcCtrlState::TestLocked6, DifLcCtrlState::Dev)
            | (DifLcCtrlState::TestLocked6, DifLcCtrlState::Prod)
            | (DifLcCtrlState::TestLocked6, DifLcCtrlState::ProdEnd)
            | (DifLcCtrlState::Dev, DifLcCtrlState::Rma)
            | (DifLcCtrlState::Prod, DifLcCtrlState::Rma) => DifLcCtrlTransCheck {
                valid: true,
                token: true,
            },
            // Transitions that do not require a token.
            (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::Rma)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::Rma)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::Rma)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::Rma)
            | (DifLcCtrlState::TestUnlocked4, DifLcCtrlState::Rma)
            | (DifLcCtrlState::TestUnlocked5, DifLcCtrlState::Rma)
            | (DifLcCtrlState::TestUnlocked6, DifLcCtrlState::Rma)
            | (DifLcCtrlState::TestUnlocked7, DifLcCtrlState::Rma)
            | (DifLcCtrlState::Raw, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked4, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked5, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked6, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked7, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestLocked0, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestLocked1, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestLocked2, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestLocked3, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestLocked4, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestLocked5, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestLocked6, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::Dev, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::Prod, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::ProdEnd, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::Rma, DifLcCtrlState::Scrap)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::TestLocked0)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::TestLocked1)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::TestLocked2)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::TestLocked3)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::TestLocked4)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::TestLocked5)
            | (DifLcCtrlState::TestUnlocked0, DifLcCtrlState::TestLocked6)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::TestLocked1)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::TestLocked2)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::TestLocked3)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::TestLocked4)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::TestLocked5)
            | (DifLcCtrlState::TestUnlocked1, DifLcCtrlState::TestLocked6)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::TestLocked2)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::TestLocked3)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::TestLocked4)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::TestLocked5)
            | (DifLcCtrlState::TestUnlocked2, DifLcCtrlState::TestLocked6)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::TestLocked3)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::TestLocked4)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::TestLocked5)
            | (DifLcCtrlState::TestUnlocked3, DifLcCtrlState::TestLocked6)
            | (DifLcCtrlState::TestUnlocked4, DifLcCtrlState::TestLocked4)
            | (DifLcCtrlState::TestUnlocked4, DifLcCtrlState::TestLocked5)
            | (DifLcCtrlState::TestUnlocked4, DifLcCtrlState::TestLocked6)
            | (DifLcCtrlState::TestUnlocked5, DifLcCtrlState::TestLocked5)
            | (DifLcCtrlState::TestUnlocked5, DifLcCtrlState::TestLocked6)
            | (DifLcCtrlState::TestUnlocked6, DifLcCtrlState::TestLocked6) => DifLcCtrlTransCheck {
                valid: true,
                token: false,
            },
            // Other transitions are invalid.
            _ => DifLcCtrlTransCheck {
                valid: false,
                token: false,
            },
        }
    }
}

#[derive(Copy, Clone)]
pub struct DifLcCtrlToken(bindgen::dif::dif_lc_ctrl_token);

impl From<[u8; 16]> for DifLcCtrlToken {
    fn from(bytes: [u8; 16]) -> Self {
        DifLcCtrlToken(bindgen::dif::dif_lc_ctrl_token { data: bytes })
    }
}

impl From<Vec<u8>> for DifLcCtrlToken {
    fn from(vector: Vec<u8>) -> Self {
        let bytes: [u8; 16] = vector.try_into().unwrap();
        DifLcCtrlToken::from(bytes)
    }
}

impl From<[u32; 4]> for DifLcCtrlToken {
    fn from(words: [u32; 4]) -> Self {
        let bytes: [u8; 16] = words
            .iter()
            .flat_map(|v| v.to_le_bytes())
            .collect::<Vec<u8>>()
            .try_into()
            .unwrap();
        DifLcCtrlToken::from(bytes)
    }
}

impl From<Vec<u32>> for DifLcCtrlToken {
    fn from(vector: Vec<u32>) -> Self {
        let bytes: [u8; 16] = vector
            .iter()
            .flat_map(|v| v.to_le_bytes())
            .collect::<Vec<u8>>()
            .try_into()
            .unwrap();
        DifLcCtrlToken::from(bytes)
    }
}

impl DifLcCtrlToken {
    /// Converts a 128-bit transition token into four native u32 words. These
    /// values are suitable to write to [LcCtrlReg::TransitionToken0] and
    /// friends.
    pub fn into_register_values(self) -> [u32; 4] {
        let mut out_words = [0u32; 4];
        let bytes = self.0.data;
        bytes
            .chunks_exact(std::mem::size_of::<u32>())
            .map(|chunk| u32::from_le_bytes(chunk.try_into().unwrap()))
            .zip(&mut out_words)
            .for_each(|(word, out)| *out = word);
        out_words
    }

    /// Returns true if the token is zero.
    pub fn is_zero(self) -> bool {
        self.0.data == [0; 16]
    }
}

#[derive(IntoPrimitive, Clone, Debug, strum::EnumString)]
#[strum(serialize_all = "snake_case")]
#[repr(u32)]
pub enum LcCtrlReg {
    AlertTest = bindgen::dif::LC_CTRL_ALERT_TEST_REG_OFFSET,
    Status = bindgen::dif::LC_CTRL_STATUS_REG_OFFSET,
    ClaimTransitionIf = bindgen::dif::LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET,
    TransitionRegwen = bindgen::dif::LC_CTRL_TRANSITION_REGWEN_REG_OFFSET,
    TransitionCmd = bindgen::dif::LC_CTRL_TRANSITION_CMD_REG_OFFSET,
    TransitionCtrl = bindgen::dif::LC_CTRL_TRANSITION_CTRL_REG_OFFSET,
    TransitionToken0 = bindgen::dif::LC_CTRL_TRANSITION_TOKEN_0_REG_OFFSET,
    TransitionToken1 = bindgen::dif::LC_CTRL_TRANSITION_TOKEN_1_REG_OFFSET,
    TransitionToken2 = bindgen::dif::LC_CTRL_TRANSITION_TOKEN_2_REG_OFFSET,
    TransitionToken3 = bindgen::dif::LC_CTRL_TRANSITION_TOKEN_3_REG_OFFSET,
    TransitionTarget = bindgen::dif::LC_CTRL_TRANSITION_TARGET_REG_OFFSET,
    OtpVendorTestCtrl = bindgen::dif::LC_CTRL_OTP_VENDOR_TEST_CTRL_REG_OFFSET,
    OtpVendorTestStatus = bindgen::dif::LC_CTRL_OTP_VENDOR_TEST_STATUS_REG_OFFSET,
    LcState = bindgen::dif::LC_CTRL_LC_STATE_REG_OFFSET,
    LcTransitionCnt = bindgen::dif::LC_CTRL_LC_TRANSITION_CNT_REG_OFFSET,
    LcIdState = bindgen::dif::LC_CTRL_LC_ID_STATE_REG_OFFSET,
    HwRevision0 = bindgen::dif::LC_CTRL_HW_REVISION0_REG_OFFSET,
    HwRevision1 = bindgen::dif::LC_CTRL_HW_REVISION1_REG_OFFSET,
    DeviceId0 = bindgen::dif::LC_CTRL_DEVICE_ID_0_REG_OFFSET,
    DeviceId1 = bindgen::dif::LC_CTRL_DEVICE_ID_1_REG_OFFSET,
    DeviceId2 = bindgen::dif::LC_CTRL_DEVICE_ID_2_REG_OFFSET,
    DeviceId3 = bindgen::dif::LC_CTRL_DEVICE_ID_3_REG_OFFSET,
    DeviceId4 = bindgen::dif::LC_CTRL_DEVICE_ID_4_REG_OFFSET,
    DeviceId5 = bindgen::dif::LC_CTRL_DEVICE_ID_5_REG_OFFSET,
    DeviceId6 = bindgen::dif::LC_CTRL_DEVICE_ID_6_REG_OFFSET,
    DeviceId7 = bindgen::dif::LC_CTRL_DEVICE_ID_7_REG_OFFSET,
    ManufState0 = bindgen::dif::LC_CTRL_MANUF_STATE_0_REG_OFFSET,
    ManufState1 = bindgen::dif::LC_CTRL_MANUF_STATE_1_REG_OFFSET,
    ManufState2 = bindgen::dif::LC_CTRL_MANUF_STATE_2_REG_OFFSET,
    ManufState3 = bindgen::dif::LC_CTRL_MANUF_STATE_3_REG_OFFSET,
    ManufState4 = bindgen::dif::LC_CTRL_MANUF_STATE_4_REG_OFFSET,
    ManufState5 = bindgen::dif::LC_CTRL_MANUF_STATE_5_REG_OFFSET,
    ManufState6 = bindgen::dif::LC_CTRL_MANUF_STATE_6_REG_OFFSET,
    ManufState7 = bindgen::dif::LC_CTRL_MANUF_STATE_7_REG_OFFSET,
}

impl LcCtrlReg {
    pub fn byte_offset(&self) -> u32 {
        self.clone().into()
    }
    /// Converts the register's byte offset into a word offset for use with DMI.
    /// <https://docs.opentitan.org/hw/ip/lc_ctrl/doc/#life-cycle-tap-controller>
    pub fn word_offset(&self) -> u32 {
        const BYTES_PER_WORD: u32 = std::mem::size_of::<u32>() as u32;
        assert_eq!(self.byte_offset() % BYTES_PER_WORD, 0);
        self.byte_offset() / BYTES_PER_WORD
    }
}

bitflags! {
    /// Bits of the lc_ctrl.STATUS register, aka [LcCtrlReg::Status].
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
    #[serde(transparent)]
    pub struct LcCtrlStatus: u32 {
        const INITIALIZED            = 0b1 << bindgen::dif::LC_CTRL_STATUS_INITIALIZED_BIT;
        const READY                  = 0b1 << bindgen::dif::LC_CTRL_STATUS_READY_BIT;
        const EXT_CLOCK_SWITCHED     = 0b1 << bindgen::dif::LC_CTRL_STATUS_EXT_CLOCK_SWITCHED_BIT;
        const TRANSITION_SUCCESSFUL  = 0b1 << bindgen::dif::LC_CTRL_STATUS_TRANSITION_SUCCESSFUL_BIT;
        const TRANSITION_COUNT_ERROR = 0b1 << bindgen::dif::LC_CTRL_STATUS_TRANSITION_COUNT_ERROR_BIT;
        const TRANSITION_ERROR       = 0b1 << bindgen::dif::LC_CTRL_STATUS_TRANSITION_ERROR_BIT;
        const TOKEN_ERROR            = 0b1 << bindgen::dif::LC_CTRL_STATUS_TOKEN_ERROR_BIT;
        const FLASH_RMA_ERROR        = 0b1 << bindgen::dif::LC_CTRL_STATUS_FLASH_RMA_ERROR_BIT;
        const OTP_ERROR              = 0b1 << bindgen::dif::LC_CTRL_STATUS_OTP_ERROR_BIT;
        const STATE_ERROR            = 0b1 << bindgen::dif::LC_CTRL_STATUS_STATE_ERROR_BIT;
        const BUS_INTEG_ERROR        = 0b1 << bindgen::dif::LC_CTRL_STATUS_BUS_INTEG_ERROR_BIT;
        const OTP_PARTITION_ERROR    = 0b1 << bindgen::dif::LC_CTRL_STATUS_OTP_PARTITION_ERROR_BIT;

        const ERRORS =
            Self::TRANSITION_COUNT_ERROR.bits() |
            Self::TRANSITION_ERROR.bits() |
            Self::TOKEN_ERROR.bits() |
            Self::FLASH_RMA_ERROR.bits() |
            Self::OTP_ERROR.bits() |
            Self::STATE_ERROR.bits() |
            Self::BUS_INTEG_ERROR.bits() |
            Self::OTP_PARTITION_ERROR.bits();
    }
}

bitflags! {
    /// Bits of the lc_ctrl.TRANSITION_REGWEN register, aka [LcCtrlReg::TransitionRegwen].
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct LcCtrlTransitionRegwen: u32 {
        const TRANSITION_REGWEN = 0b1 << bindgen::dif::LC_CTRL_TRANSITION_REGWEN_TRANSITION_REGWEN_BIT;
    }
}

bitflags! {
    /// Bits of the lc_ctrl.TRANSITION_CMD register, aka [LcCtrlReg::TransitionCmd].
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct LcCtrlTransitionCmd: u32 {
        const START = 0b1 << bindgen::dif::LC_CTRL_TRANSITION_CMD_START_BIT;
    }
}

bitflags! {
    /// Bits of the lc_ctrl.TRANSITION_CTRL register, aka [LcCtrlReg::TransitionCtrl].
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct LcCtrlTransitionCtrl: u32 {
        const EXT_CLOCK_EN = 0b1 << bindgen::dif::LC_CTRL_TRANSITION_CTRL_EXT_CLOCK_EN_BIT;
        const VOLATILE_RAW_UNLOCK = 0b1 << bindgen::dif::LC_CTRL_TRANSITION_CTRL_VOLATILE_RAW_UNLOCK_BIT;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Raw is zero, so its redundant encoding is a fixed point.
    #[test]
    fn lc_ctrl_state_redundant_encoding_zero() {
        assert_eq!(u32::from(DifLcCtrlState::Raw), 0);
        assert_eq!(DifLcCtrlState::Raw.redundant_encoding(), 0);
    }

    /// The redundant encoding of non-zero values shouldn't be a fixed point.
    #[test]
    fn lc_ctrl_state_redundant_encoding_nonzero() {
        assert_ne!(
            u32::from(DifLcCtrlState::Rma),
            DifLcCtrlState::Rma.redundant_encoding()
        );
        assert_eq!(DifLcCtrlState::Rma.redundant_encoding(), 0x2739ce73);
    }

    #[test]
    fn lc_ctrl_token() {
        // This test assumes the system is little-endian.
        let token_bytes: [u8; 16] = [
            0x01, 0x02, 0x03, 0x04, // TOKEN_0
            0x11, 0x12, 0x13, 0x14, // TOKEN_1
            0x21, 0x22, 0x23, 0x24, // TOKEN_2
            0x31, 0x32, 0x33, 0x34, // TOKEN_3
        ];
        let token = DifLcCtrlToken::from(token_bytes);
        let words: [u32; 4] = token.into_register_values();
        assert_eq!(words, [0x04030201, 0x14131211, 0x24232221, 0x34333231]);
    }

    #[test]
    fn lc_ctrl_register_offsets() {
        let offset = bindgen::dif::LC_CTRL_LC_STATE_REG_OFFSET;
        assert_eq!(LcCtrlReg::LcState.byte_offset(), offset);
        assert_eq!(LcCtrlReg::LcState.word_offset(), offset / 4);
    }

    #[test]
    fn lc_status_bits() {
        assert_eq!(LcCtrlStatus::empty(), LcCtrlStatus::from_bits_truncate(0));
        assert_eq!(
            LcCtrlStatus::INITIALIZED,
            LcCtrlStatus::from_bits_truncate(1)
        );
        assert_eq!(
            LcCtrlStatus::INITIALIZED | LcCtrlStatus::READY,
            LcCtrlStatus::from_bits_truncate(3)
        );

        let ready = LcCtrlStatus::INITIALIZED | LcCtrlStatus::READY;
        assert!(ready.contains(LcCtrlStatus::READY));
        assert!(!ready.contains(LcCtrlStatus::TRANSITION_SUCCESSFUL));
    }
}
