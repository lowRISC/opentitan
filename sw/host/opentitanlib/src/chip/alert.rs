// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;

with_unknown! {
    pub enum AlertClass: u8 {
        A = bindgen::alert::AlertClass_kAlertClassA as u8,
        B = bindgen::alert::AlertClass_kAlertClassB as u8,
        C = bindgen::alert::AlertClass_kAlertClassC as u8,
        D = bindgen::alert::AlertClass_kAlertClassD as u8,
        X = bindgen::alert::AlertClass_kAlertClassX as u8,
    }
}

with_unknown! {
    pub enum AlertEnable: u8 {
        None = bindgen::alert::AlertEnable_kAlertEnableNone as u8,
        Enabled = bindgen::alert::AlertEnable_kAlertEnableEnabled as u8,
        Locked = bindgen::alert::AlertEnable_kAlertEnableLocked as u8,
    }
}

with_unknown! {
    pub enum AlertEscalate: u8 {
        None = bindgen::alert::AlertEscalate_kAlertEscalateNone as u8,
        Phase0 = bindgen::alert::AlertEscalate_kAlertEscalatePhase0 as u8,
        Phase1 = bindgen::alert::AlertEscalate_kAlertEscalatePhase1 as u8,
        Phase2 = bindgen::alert::AlertEscalate_kAlertEscalatePhase2 as u8,
        Phase3 = bindgen::alert::AlertEscalate_kAlertEscalatePhase3 as u8,
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
