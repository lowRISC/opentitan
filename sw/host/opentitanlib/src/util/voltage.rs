// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use std::num::ParseFloatError;
use std::str::FromStr;

#[derive(Debug, Default, Clone, Copy, Serialize, Deserialize)]
pub struct Voltage(pub f64);

impl FromStr for Voltage {
    type Err = ParseFloatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Allow voltages to be specified as they are in schematics: "3v3", "1v8", etc.
        let voltage = s.to_lowercase().replace('v', ".");
        Ok(Voltage(f64::from_str(&voltage)?))
    }
}

impl Voltage {
    pub fn as_volts(&self) -> f64 {
        self.0
    }
    pub fn as_millivolts(&self) -> u32 {
        (self.0 * 1000.0) as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    #[test]
    fn test_from_string() -> Result<()> {
        assert_eq!(Voltage::from_str("3.3")?.as_volts(), 3.3);
        assert_eq!(Voltage::from_str("3v3")?.as_volts(), 3.3);
        assert_eq!(Voltage::from_str("1V8")?.as_volts(), 1.8);
        assert!(Voltage::from_str("1k4").is_err());
        Ok(())
    }

    #[test]
    fn test_conversions() -> Result<()> {
        assert_eq!(Voltage(2.5).as_volts(), 2.5);
        assert_eq!(Voltage(2.5).as_millivolts(), 2500);
        assert_eq!(Voltage(3.141592654).as_millivolts(), 3141);
        Ok(())
    }
}
