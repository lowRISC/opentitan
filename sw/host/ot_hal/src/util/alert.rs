// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

with_unknown! {
    pub enum AlertClass: u8 {
        A = ot_bindgen_alert::AlertClass_kAlertClassA as u8,
        B = ot_bindgen_alert::AlertClass_kAlertClassB as u8,
        C = ot_bindgen_alert::AlertClass_kAlertClassC as u8,
        D = ot_bindgen_alert::AlertClass_kAlertClassD as u8,
        X = ot_bindgen_alert::AlertClass_kAlertClassX as u8,
    }
}

with_unknown! {
    pub enum AlertEnable: u8 {
        None = ot_bindgen_alert::AlertEnable_kAlertEnableNone as u8,
        Enabled = ot_bindgen_alert::AlertEnable_kAlertEnableEnabled as u8,
        Locked = ot_bindgen_alert::AlertEnable_kAlertEnableLocked as u8,
    }
}

with_unknown! {
    pub enum AlertEscalate: u8 {
        None = ot_bindgen_alert::AlertEscalate_kAlertEscalateNone as u8,
        Phase0 = ot_bindgen_alert::AlertEscalate_kAlertEscalatePhase0 as u8,
        Phase1 = ot_bindgen_alert::AlertEscalate_kAlertEscalatePhase1 as u8,
        Phase2 = ot_bindgen_alert::AlertEscalate_kAlertEscalatePhase2 as u8,
        Phase3 = ot_bindgen_alert::AlertEscalate_kAlertEscalatePhase3 as u8,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    #[test]
    fn test_trivial_values() -> Result<()> {
        // Class A has value 238.
        assert_eq!(AlertClass::A, AlertClass(238));
        // AlertEnable Locked has value 210.
        assert_eq!(AlertEnable::Locked, AlertEnable(210));
        // AlertEscalate Phase0 has value 185.
        assert_eq!(AlertEscalate::Phase0, AlertEscalate(185));
        Ok(())
    }
}
