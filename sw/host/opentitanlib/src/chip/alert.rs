// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use bindgen_alert;

with_unknown! {
    pub enum AlertClass: u8 {
        A = bindgen_alert::AlertClass_kAlertClassA,
        B = bindgen_alert::AlertClass_kAlertClassB,
        C = bindgen_alert::AlertClass_kAlertClassC,
        D = bindgen_alert::AlertClass_kAlertClassD,
        X = bindgen_alert::AlertClass_kAlertClassX,
    }
}

with_unknown! {
    pub enum AlertEnable: u8 {
        None = bindgen_alert::AlertEnable_kAlertEnableNone,
        Enabled = bindgen_alert::AlertEnable_kAlertEnableEnabled,
        Locked = bindgen_alert::AlertEnable_kAlertEnableLocked,
    }
}

with_unknown! {
    pub enum AlertEscalate: u8 {
        None = bindgen_alert::AlertEscalate_kAlertEscalateNone,
        Phase0 = bindgen_alert::AlertEscalate_kAlertEscalatePhase0,
        Phase1 = bindgen_alert::AlertEscalate_kAlertEscalatePhase1,
        Phase2 = bindgen_alert::AlertEscalate_kAlertEscalatePhase2,
        Phase3 = bindgen_alert::AlertEscalate_kAlertEscalatePhase3,
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
    }
}
