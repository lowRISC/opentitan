// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use num_bigint_dig::BigUint;
use num_traits::Num;
use std::cmp::Ordering;
use std::fmt;
use std::iter;
use thiserror::Error;

use crate::util::parse_int::ParseInt;

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum ParseBigIntError {
    #[error("integer is too large")]
    Overflow,
    #[error("integer is too small")]
    Underflow,
    #[error(transparent)]
    ParseBigIntError(#[from] num_bigint_dig::ParseBigIntError),
}

/// A fixed-size unsigned big integer.
///
/// This struct wraps a `BigUint` to facilitate defining new fixed-size unsigned integer types for
/// better type safety.
///
/// An integer stored in this type is fixed-size in the sense that the minimum number of bits
/// required to represent it, i.e. its bit length, is at most `BIT_LEN`. This size can be specified
/// using the const parameters `BIT_LEN` and `EXACT_LEN` as follows:
///   - When `EXACT_LEN` is `false`, the bit length of the integer can be at most `BIT_LEN` bits,
///     e.g. SHA-256 digests (at most 256 bits) or RSA-3072 signatures (at most 3072 bits),
///   - When `EXACT_LEN` is `true`, the number of bits required to represent the integer must be
///     exactly `BIT_LEN` bits, e.g. RSA-3072 moduli (exactly 3072 bits).
/// Note that while the type encapsulates the size information, the actual check is performed at
/// runtime when an instance is created (see `check_len()`).
///
/// This struct is not meant to be used directly, please see the `fixed_size_bigint` macro which
/// also generates the required boilerplate code for new types.
#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct FixedSizeBigInt<const BIT_LEN: usize, const EXACT_LEN: bool>(BigUint);

impl<const BIT_LEN: usize, const EXACT_LEN: bool> FixedSizeBigInt<BIT_LEN, EXACT_LEN> {
    const BYTE_LEN: usize = BIT_LEN.saturating_add(u8::BITS as usize - 1) / u8::BITS as usize;

    /// Checks the bit length of the `FixedSizeBigInt`.
    ///
    /// Bit length of a `FixedSizeBigInt` can be at most `BIT_LEN` if `EXACT_LEN` is `false`, must
    /// be exactly `BIT_LEN` otherwise.
    fn new_from_biguint(biguint: BigUint) -> Result<Self, ParseBigIntError> {
        match (biguint.bits().cmp(&BIT_LEN), EXACT_LEN) {
            (Ordering::Greater, _) => Err(ParseBigIntError::Overflow),
            (Ordering::Equal, _) => Ok(Self(biguint)),
            (Ordering::Less, true) => Err(ParseBigIntError::Underflow),
            (Ordering::Less, false) => Ok(Self(biguint)),
        }
    }

    /// Creates a `FixedSizeBigInt` from little-endian bytes.
    pub(crate) fn from_le_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, ParseBigIntError> {
        Self::new_from_biguint(BigUint::from_bytes_le(bytes.as_ref()))
    }

    /// Creates a `FixedSizeBigInt` from big-endian bytes.
    pub(crate) fn from_be_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, ParseBigIntError> {
        Self::new_from_biguint(BigUint::from_bytes_be(bytes.as_ref()))
    }

    /// Returns the bit length.
    ///
    /// Bit length of `FixedSizeBigInt` is the minimum number of bits required to represent its
    /// value. The underlying storage may be larger.
    pub(crate) fn bit_len(&self) -> usize {
        self.0.bits()
    }

    /// Returns the byte representation in little-endian order.
    pub(crate) fn to_le_bytes(&self) -> Vec<u8> {
        let mut v = self.0.to_bytes_le();
        assert!(Self::BYTE_LEN >= v.len());
        // Append since `v` is little-endian.
        v.resize(Self::BYTE_LEN, 0);
        v
    }

    /// Returns the byte representation in big-endian order.
    pub(crate) fn to_be_bytes(&self) -> Vec<u8> {
        let mut v = self.0.to_bytes_be();
        assert!(Self::BYTE_LEN >= v.len());
        // Prepend since `v` is big-endian.
        v.splice(0..0, iter::repeat(0).take(Self::BYTE_LEN - v.len()));
        v
    }

    /// Returns the underlying `BigUint`.
    pub(crate) fn as_biguint(&self) -> &BigUint {
        &self.0
    }
}

impl<const BIT_LEN: usize, const EXACT_LEN: bool> ParseInt for FixedSizeBigInt<BIT_LEN, EXACT_LEN> {
    type FromStrRadixErr = ParseBigIntError;

    fn from_str_radix(src: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Self::new_from_biguint(
            BigUint::from_str_radix(src, radix).map_err(ParseBigIntError::ParseBigIntError)?,
        )
    }
}

impl<const BIT_LEN: usize, const EXACT_LEN: bool> fmt::Display
    for FixedSizeBigInt<BIT_LEN, EXACT_LEN>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(
            &format_args!("{:#0width$x}", self.0, width = Self::BYTE_LEN * 2 + 2),
            f,
        )
    }
}

/// Helper macro for the `fixed_size_bigint` macro.
macro_rules! fixed_size_bigint_impl {
    ($struct_name:ident, $bit_len:expr, $exact_len:expr) => {
        #[derive(serde::Serialize, Debug, Clone, Eq, PartialEq)]
        #[serde(into = "String")]
        pub struct $struct_name($crate::util::bigint::FixedSizeBigInt<$bit_len, $exact_len>);

        const _: () = {
            use num_bigint_dig::BigUint;
            use std::fmt;
            use std::result::Result;

            use $crate::util::bigint::{FixedSizeBigInt, ParseBigIntError};
            use $crate::util::parse_int::ParseInt;

            impl $struct_name {
                pub fn from_le_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, ParseBigIntError> {
                    Ok($struct_name(
                        FixedSizeBigInt::<$bit_len, $exact_len>::from_le_bytes(bytes)?,
                    ))
                }

                pub fn from_be_bytes(bytes: impl AsRef<[u8]>) -> Result<Self, ParseBigIntError> {
                    Ok($struct_name(
                        FixedSizeBigInt::<$bit_len, $exact_len>::from_be_bytes(bytes)?,
                    ))
                }

                pub fn bit_len(&self) -> usize {
                    self.0.bit_len()
                }

                pub fn to_le_bytes(&self) -> Vec<u8> {
                    self.0.to_le_bytes()
                }

                pub fn to_be_bytes(&self) -> Vec<u8> {
                    self.0.to_be_bytes()
                }

                pub fn as_biguint(&self) -> &BigUint {
                    self.0.as_biguint()
                }
            }

            impl ParseInt for $struct_name {
                type FromStrRadixErr = ParseBigIntError;

                fn from_str_radix(src: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                    Ok($struct_name(
                        FixedSizeBigInt::<$bit_len, $exact_len>::from_str_radix(src, radix)?,
                    ))
                }
            }

            impl fmt::Display for $struct_name {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    fmt::Display::fmt(&self.0, f)
                }
            }

            impl From<$struct_name> for String {
                fn from(s: $struct_name) -> String {
                    s.0.to_string()
                }
            }
        };
    };
}

pub(crate) use fixed_size_bigint_impl;

/// Macro for defining a new fixed-size unsigned big integer type.
///
/// Defines a new type that wraps a `FixedSizeBigInt`. This macro is intended to be used within this
/// crate to define types which can then be exported as needed:
///
/// ```
/// use crate::util::bigint::fixed_size_bigint;
///
/// // Define a type for RSA-3072 moduli (exactly 3072 bits long):
/// fixed_size_bigint!(Rsa3072Modulus, 3072);
///
/// // Define a type for SHA-256 digests (at most 256 bits long):
/// fixed_size_bigint!(Sha256Digest, at_most 256);
/// ```
macro_rules! fixed_size_bigint {
    ($struct_name:ident, $bit_len:expr) => {
        $crate::util::bigint::fixed_size_bigint_impl!($struct_name, $bit_len, true);
    };
    ($struct_name:ident, at_most $bit_len:expr) => {
        $crate::util::bigint::fixed_size_bigint_impl!($struct_name, $bit_len, false);
    };
}

pub(crate) use fixed_size_bigint;

#[cfg(test)]
mod tests {
    use super::*;

    fixed_size_bigint!(TestArray, at_most 16);
    fixed_size_bigint!(TestArrayExact, 16);

    #[test]
    fn test_from_to_le_bytes() {
        fn check(slice: &[u8], data: &[u8]) {
            assert_eq!(TestArray::from_le_bytes(slice).unwrap().to_le_bytes(), data);
        }
        check(&[], &[0, 0]);
        check(&[1], &[1, 0]);
        check(&[0, 1], &[0, 1]);
        check(&[1, 0], &[1, 0]);

        assert!(TestArray::from_le_bytes([1, 2, 3]).is_err());
    }

    #[test]
    fn test_from_to_le_bytes_exact_len() {
        fn check(slice: &[u8], data: &[u8]) {
            assert_eq!(
                TestArrayExact::from_le_bytes(slice).unwrap().to_le_bytes(),
                data
            );
        }
        check(&[0, 128], &[0, 128]);
        check(&[255, 255, 0], &[255, 255]);

        assert!(TestArrayExact::from_le_bytes([1]).is_err());
        assert!(TestArrayExact::from_le_bytes([255, 127]).is_err());
        assert!(TestArrayExact::from_le_bytes([0, 0, 1]).is_err());
    }

    #[test]
    fn test_from_to_be_bytes() {
        fn check(slice: &[u8], data: &[u8]) {
            assert_eq!(TestArray::from_be_bytes(slice).unwrap().to_be_bytes(), data);
        }
        check(&[1], &[0, 1]);
        check(&[1, 0], &[1, 0]);
        check(&[0, 1], &[0, 1]);

        assert!(TestArray::from_be_bytes([1, 2, 1]).is_err());
    }

    #[test]
    fn test_from_to_be_bytes_exact_len() {
        fn check(slice: &[u8], data: &[u8]) {
            assert_eq!(
                TestArrayExact::from_be_bytes(slice).unwrap().to_be_bytes(),
                data
            );
        }
        check(&[128, 1], &[128, 1]);
        check(&[0, 255, 255], &[255, 255]);

        assert!(TestArrayExact::from_be_bytes([1]).is_err());
        assert!(TestArrayExact::from_be_bytes([127, 1]).is_err());
        assert!(TestArrayExact::from_be_bytes([1, 0, 0]).is_err());
    }

    #[test]
    fn test_bit_len() {
        fn check(slice: &[u8], bit_len: usize) {
            assert_eq!(TestArray::from_le_bytes(slice).unwrap().bit_len(), bit_len);
        }
        check(&[1], 1);
        check(&[1, 0], 1);
        check(&[255], 8);
        check(&[0, 1], 9);
        check(&[0, 128], 16);
    }

    #[test]
    fn test_from_str() {
        assert_eq!(TestArray::from_str("0x01").unwrap().to_le_bytes(), [1, 0]);
        assert_eq!(
            TestArray::from_str("0x00201").unwrap().to_le_bytes(),
            [1, 2]
        );
        assert!(TestArray::from_str("0x030201").is_err());
    }

    #[test]
    fn test_from_str_exact_len() {
        assert_eq!(
            TestArrayExact::from_str("0x08001").unwrap().to_le_bytes(),
            [1, 128]
        );

        assert!(TestArrayExact::from_str("0x01").is_err());
        assert!(TestArrayExact::from_str("0x0201").is_err());
        assert!(TestArrayExact::from_str("0x030201").is_err());
    }

    #[test]
    fn test_fmt() {
        let exact = TestArrayExact::from_str("0xabcd").unwrap();
        assert_eq!(exact.to_string(), "0xabcd");

        let at_most = TestArray::from_str("0xab").unwrap();
        assert_eq!(at_most.to_string(), "0x00ab");

        let at_most_full = TestArray::from_str("0xabcd").unwrap();
        assert_eq!(at_most_full.to_string(), "0xabcd");
    }
}
