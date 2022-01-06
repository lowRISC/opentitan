// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::util::parse_int::{ParseInt, ParseIntError};

use anyhow::Result;

impl ParseInt for Vec<u8> {
    type FromStrRadixErr = ParseIntError;

    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        let mut bytes = vec![];
        for digit_bytes in src.as_bytes().rchunks(2) {
            let digits = std::str::from_utf8(digit_bytes).unwrap();
            bytes.push(u8::from_str_radix(digits, radix)?);
        }
        Ok(bytes)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::convert::TryInto;
    #[test]
    fn byte_field_test() {
        assert_eq!(Vec::from_str("0x1"), Ok(vec![0x1]));
        assert_eq!(
            Vec::from_str("0x4b4b4b4b4b4ba5a5"),
            Ok(vec![0xa5, 0xa5, 0x4b, 0x4b, 0x4b, 0x4b, 0x4b, 0x4b])
        );
        assert_eq!(
            u64::from_ne_bytes(
                Vec::from_str("0x4b4b4b4b4b4ba5a5")
                    .unwrap()
                    .try_into()
                    .unwrap()
            ),
            u64::from_str("0x4b4b4b4b4b4ba5a5").unwrap()
        );
        assert!(Vec::from_str("-1").is_err());
    }
}
