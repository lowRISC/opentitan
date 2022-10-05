// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;
use bindgen_alert;

with_unknown! {
    pub enum AlertClass: u8 {
        A = bindgen_alert::AlertClass_kAlertClassA as u8,
        B = bindgen_alert::AlertClass_kAlertClassB as u8,
        C = bindgen_alert::AlertClass_kAlertClassC as u8,
        D = bindgen_alert::AlertClass_kAlertClassD as u8,
        X = bindgen_alert::AlertClass_kAlertClassX as u8,
    }
}

with_unknown! {
    pub enum AlertEnable: u8 {
        None = bindgen_alert::AlertEnable_kAlertEnableNone as u8,
        Enabled = bindgen_alert::AlertEnable_kAlertEnableEnabled as u8,
        Locked = bindgen_alert::AlertEnable_kAlertEnableLocked as u8,
    }
}

with_unknown! {
    pub enum AlertEscalate: u8 {
        None = bindgen_alert::AlertEscalate_kAlertEscalateNone as u8,
        Phase0 = bindgen_alert::AlertEscalate_kAlertEscalatePhase0 as u8,
        Phase1 = bindgen_alert::AlertEscalate_kAlertEscalatePhase1 as u8,
        Phase2 = bindgen_alert::AlertEscalate_kAlertEscalatePhase2 as u8,
        Phase3 = bindgen_alert::AlertEscalate_kAlertEscalatePhase3 as u8,
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
