// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::num;
use thiserror::Error;

#[derive(Error, Debug, Clone, Eq, PartialEq)]
pub enum ParseIntError {
    #[error(transparent)]
    ParseIntError(#[from] num::ParseIntError),
}

/// Trait for parsing integers.
///
/// Strings beginning with the common and classic prefixes `0x`, `0o`, `0b` or `0` are parsed
/// as hex, octal, binary, and octal (classic).  Anything else is parsed as decimal.
/// A leading `+` or `-` is permitted.  Any string parsed by `strtol(3)` or `strtoul(3)`
/// will be parsed successfully.
pub trait ParseInt: Sized {
    type FromStrRadixErr: Into<ParseIntError>;

    fn from_str_radix(src: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr>;

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        let (val, negative) = if let Some(v) = src.strip_prefix('-') {
            (v, true)
        } else if let Some(v) = src.strip_prefix('+') {
            (v, false)
        } else {
            (src, false)
        };

        let (radix, digits) = match val.get(0..2) {
            Some("0x") | Some("0X") => (16, &val[2..]),
            Some("0o") | Some("0O") => (8, &val[2..]),
            Some("0b") | Some("0B") => (2, &val[2..]),
            _ if val.starts_with('0') => (8, val),
            _ => (10, val),
        };

        if negative {
            let mut digits = digits.to_string();
            digits.insert(0, '-');
            Self::from_str_radix(&digits, radix).map_err(Self::FromStrRadixErr::into)
        } else {
            Self::from_str_radix(digits, radix).map_err(Self::FromStrRadixErr::into)
        }
    }
}

macro_rules! impl_parse_int {
    ($ty:ident) => {
        impl ParseInt for $ty {
            type FromStrRadixErr = num::ParseIntError;

            fn from_str_radix(src: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                $ty::from_str_radix(src, radix)
            }
        }
    };
}

impl_parse_int!(i8);
impl_parse_int!(u8);
impl_parse_int!(i16);
impl_parse_int!(u16);
impl_parse_int!(i32);
impl_parse_int!(u32);
impl_parse_int!(i64);
impl_parse_int!(u64);
impl_parse_int!(isize);
impl_parse_int!(usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_i8() {
        assert_eq!(i8::from_str("0"), Ok(0));
        assert_eq!(i8::from_str("-1"), Ok(-1));
        assert_eq!(i8::from_str("+100"), Ok(100));
        assert_eq!(i8::from_str("-128"), Ok(-128));
        assert_eq!(i8::from_str("0x10"), Ok(16));
        assert_eq!(i8::from_str("-0x10"), Ok(-16));
        assert_eq!(i8::from_str("0o10"), Ok(8));
        assert_eq!(i8::from_str("-0o10"), Ok(-8));
        assert_eq!(i8::from_str("0b10"), Ok(2));
        assert_eq!(i8::from_str("-0b10"), Ok(-2));
        assert_eq!(i8::from_str("012"), Ok(10));
        assert!(i8::from_str("128").is_err());
        assert!(i8::from_str("-129").is_err());
    }

    #[test]
    fn test_u8() {
        assert_eq!(u8::from_str("0"), Ok(0));
        assert_eq!(u8::from_str("+100"), Ok(100));
        assert_eq!(u8::from_str("128"), Ok(128));
        assert_eq!(u8::from_str("255"), Ok(255));
        assert_eq!(u8::from_str("0x10"), Ok(16));
        assert_eq!(u8::from_str("0xFF"), Ok(255));
        assert_eq!(u8::from_str("0o10"), Ok(8));
        assert_eq!(u8::from_str("0b10000000"), Ok(128));
        assert_eq!(u8::from_str("012"), Ok(10));
        assert!(u8::from_str("-1").is_err());
        assert!(u8::from_str("256").is_err());
    }

    #[test]
    fn test_i16() {
        assert_eq!(i16::from_str("0"), Ok(0));
        assert_eq!(i16::from_str("-1"), Ok(-1));
        assert_eq!(i16::from_str("+32767"), Ok(32767));
        assert_eq!(i16::from_str("-32768"), Ok(-32768));
        assert_eq!(i16::from_str("0x3fff"), Ok(16383));
        assert_eq!(i16::from_str("-0x10"), Ok(-16));
        assert_eq!(i16::from_str("0o10"), Ok(8));
        assert_eq!(i16::from_str("-0o10"), Ok(-8));
        assert_eq!(i16::from_str("0b10"), Ok(2));
        assert_eq!(i16::from_str("-0b10"), Ok(-2));
        assert_eq!(i16::from_str("012"), Ok(10));
        assert!(i16::from_str("32768").is_err());
        assert!(i16::from_str("-32769").is_err());
    }

    #[test]
    fn test_u16() {
        assert_eq!(u16::from_str("0"), Ok(0));
        assert_eq!(u16::from_str("+100"), Ok(100));
        assert_eq!(u16::from_str("32768"), Ok(32768));
        assert_eq!(u16::from_str("65535"), Ok(65535));
        assert_eq!(u16::from_str("0x10"), Ok(16));
        assert_eq!(u16::from_str("0xFF"), Ok(255));
        assert_eq!(u16::from_str("0o10"), Ok(8));
        assert_eq!(u16::from_str("0b1000000000000000"), Ok(32768));
        assert_eq!(u16::from_str("012"), Ok(10));
        assert!(u16::from_str("-1").is_err());
        assert!(u16::from_str("65536").is_err());
    }

    #[test]
    fn test_i32() {
        assert_eq!(i32::from_str("0"), Ok(0));
        assert_eq!(i32::from_str("-1"), Ok(-1));
        assert_eq!(i32::from_str("+2147483647"), Ok(2147483647));
        assert_eq!(i32::from_str("-2147483648"), Ok(-2147483648));
        assert_eq!(i32::from_str("0x7fffffff"), Ok(2147483647));
        assert_eq!(i32::from_str("-0x10"), Ok(-16));
        assert_eq!(i32::from_str("0o10"), Ok(8));
        assert_eq!(i32::from_str("-0o10"), Ok(-8));
        assert_eq!(i32::from_str("0b10"), Ok(2));
        assert_eq!(i32::from_str("-0b10"), Ok(-2));
        assert_eq!(i32::from_str("012"), Ok(10));
        assert!(i32::from_str("2147483648").is_err());
        assert!(i32::from_str("-2147483649").is_err());
    }

    #[test]
    fn test_u32() {
        assert_eq!(u32::from_str("0"), Ok(0));
        assert_eq!(u32::from_str("+100"), Ok(100));
        assert_eq!(u32::from_str("2147483648"), Ok(2147483648));
        assert_eq!(u32::from_str("4294967295"), Ok(4294967295));
        assert_eq!(u32::from_str("0x10"), Ok(16));
        assert_eq!(u32::from_str("0xFF"), Ok(255));
        assert_eq!(u32::from_str("0o10"), Ok(8));
        assert_eq!(u32::from_str("012"), Ok(10));
        assert_eq!(
            u32::from_str("0b10000000000000000000000000000000"),
            Ok(2147483648)
        );
        assert!(u32::from_str("-1").is_err());
        assert!(u32::from_str("4294967296").is_err());
    }

    #[test]
    fn test_i64() {
        assert_eq!(i64::from_str("0"), Ok(0));
        assert_eq!(i64::from_str("-1"), Ok(-1));
        assert_eq!(
            i64::from_str("+9223372036854775807"),
            Ok(9223372036854775807)
        );
        assert_eq!(
            i64::from_str("-9223372036854775808"),
            Ok(-9223372036854775808)
        );
        assert_eq!(i64::from_str("0x7fffffff"), Ok(2147483647));
        assert_eq!(i64::from_str("-0x10"), Ok(-16));
        assert_eq!(i64::from_str("0o10"), Ok(8));
        assert_eq!(i64::from_str("-0o10"), Ok(-8));
        assert_eq!(i64::from_str("0b10"), Ok(2));
        assert_eq!(i64::from_str("-0b10"), Ok(-2));
        assert_eq!(i64::from_str("012"), Ok(10));
        assert!(i64::from_str("9223372036854775808").is_err());
        assert!(i64::from_str("-9223372036854775809").is_err());
    }

    #[test]
    fn test_u64() {
        assert_eq!(u64::from_str("0"), Ok(0));
        assert_eq!(u64::from_str("+100"), Ok(100));
        assert_eq!(
            u64::from_str("+9223372036854775808"),
            Ok(9223372036854775808)
        );
        assert_eq!(
            u64::from_str("18446744073709551615"),
            Ok(18446744073709551615)
        );
        assert_eq!(u64::from_str("0x10"), Ok(16));
        assert_eq!(u64::from_str("0xFF"), Ok(255));
        assert_eq!(u64::from_str("0o10"), Ok(8));
        assert_eq!(
            u64::from_str("0b10000000000000000000000000000000"),
            Ok(2147483648)
        );
        assert_eq!(u64::from_str("012"), Ok(10));
        assert!(u64::from_str("-1").is_err());
        assert!(u64::from_str("18446744073709551616").is_err());
    }

    #[test]
    fn test_isize() {
        // Since isize's size is target defined, we don't bother with
        // trying to test large values and assume the tests for the
        // other integer types will cover the values for isize.
        assert_eq!(isize::from_str("0"), Ok(0));
        assert_eq!(isize::from_str("-1"), Ok(-1));
        assert_eq!(isize::from_str("0x7f"), Ok(127));
        assert_eq!(isize::from_str("-0x10"), Ok(-16));
        assert_eq!(isize::from_str("0o10"), Ok(8));
        assert_eq!(isize::from_str("-0o10"), Ok(-8));
        assert_eq!(isize::from_str("0b10"), Ok(2));
        assert_eq!(isize::from_str("-0b10"), Ok(-2));
        assert_eq!(isize::from_str("012"), Ok(10));
    }

    #[test]
    fn test_usize() {
        // Since usize's size is target defined, we don't bother with
        // trying to test large values and assume the tests for the
        // other integer types will cover the values for usize.
        assert_eq!(usize::from_str("0"), Ok(0));
        assert_eq!(usize::from_str("+100"), Ok(100));
        assert_eq!(usize::from_str("0x10"), Ok(16));
        assert_eq!(usize::from_str("0xFF"), Ok(255));
        assert_eq!(usize::from_str("0o10"), Ok(8));
        assert_eq!(usize::from_str("012"), Ok(10));
        assert!(usize::from_str("-1").is_err());
    }
}
