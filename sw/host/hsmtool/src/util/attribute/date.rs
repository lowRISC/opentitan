// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use cryptoki::types;
use cryptoki_sys::*;
use std::convert::TryFrom;

use crate::util::attribute::{AttrData, AttributeError};

pub struct Date(pub String);

fn parse(s: &[u8]) -> u32 {
    let mut result = 0;
    for &byte in s.iter() {
        let ch = byte as char;
        if ch.is_ascii_whitespace() || ch == '\0' {
            // do nothing
        } else if ch.is_ascii_digit() {
            result *= 10;
            result += (byte - b'0') as u32;
        } else {
            panic!("Expected digit or whitespace in {:?}", s);
        }
    }
    result
}

impl From<types::Date> for Date {
    fn from(val: types::Date) -> Self {
        let val = CK_DATE::from(val);
        let year = parse(&val.year);
        let month = parse(&val.month);
        let day = parse(&val.day);
        Date(format!("{:04}-{:02}-{:02}", year, month, day))
    }
}

impl From<&str> for Date {
    fn from(val: &str) -> Self {
        Date(val.to_string())
    }
}

impl From<Date> for String {
    fn from(val: Date) -> Self {
        val.0
    }
}

impl TryFrom<Date> for types::Date {
    type Error = cryptoki::error::Error;
    fn try_from(val: Date) -> Result<Self, Self::Error> {
        if val.0.len() == 8 {
            // Date in the form YYYYMMDD.
            types::Date::new_from_str_slice(&val.0[0..4], &val.0[4..6], &val.0[6..8])
        } else if val.0.len() == 10 {
            // Date in the form YYYY-MM-DD.
            types::Date::new_from_str_slice(&val.0[0..4], &val.0[5..7], &val.0[8..10])
        } else {
            Err(cryptoki::error::Error::InvalidValue)
        }
    }
}

impl TryFrom<&AttrData> for Date {
    type Error = AttributeError;
    fn try_from(val: &AttrData) -> Result<Self, Self::Error> {
        Ok(Self::from(val.try_str()?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    #[test]
    fn test_convert_to_cryptoki_date() -> Result<()> {
        let d = Date::from("2023-02-01");
        let k = types::Date::try_from(d)?;
        assert_eq!(k.to_string(), "Month: 02\nDay: 01\nYear: 2023");

        let d = Date::from("20230504");
        let k = types::Date::try_from(d)?;
        assert_eq!(k.to_string(), "Month: 05\nDay: 04\nYear: 2023");

        let d = Date::from("1234");
        assert!(types::Date::try_from(d).is_err());
        Ok(())
    }

    #[test]
    fn test_convert_from_cryptoki_date() -> Result<()> {
        let k = types::Date::from(CK_DATE {
            year: *b"2023",
            month: *b"02",
            day: *b"01",
        });
        let d = Date::from(k);
        assert_eq!(String::from(d), "2023-02-01");

        let k = types::Date::from(CK_DATE {
            year: *b"2023",
            month: *b" 5",
            day: *b"4 ",
        });
        let d = Date::from(k);
        assert_eq!(String::from(d), "2023-05-04");

        Ok(())
    }
}
