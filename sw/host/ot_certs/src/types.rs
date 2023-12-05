// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use num_bigint_dig::BigUint;
use rand::distributions::Distribution;

use crate::template::{Conversion, VariableType};

// This trait encodes information about an ASN1 type.
pub trait Type<T: Clone> {
    // Return the corresponding VariableType describing how this value is encoded in ASN1.
    // A size of 0 means that the size is unspecified.
    fn variable_type() -> VariableType;

    // Given a size in bytes, return a randomly generated array of bytes and the corresponding
    // value of type T. The generated value must be so that it ensures that the ASN1 encoder
    // will have to use exactly the specified number of bytes and not less or more. The array of
    // bytes must the ASN1 encoding of that value.
    fn random_value(size: usize) -> (Vec<u8>, T);
}

impl Type<Vec<u8>> for Vec<u8> {
    fn variable_type() -> VariableType {
        VariableType::ByteArray { size: 0 }
    }

    fn random_value(size: usize) -> (Vec<u8>, Vec<u8>) {
        // Generate a random byte array.
        let bytes = (0..size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
        let copy = bytes.clone();
        (bytes, copy)
    }
}

impl Type<BigUint> for BigUint {
    fn variable_type() -> VariableType {
        // ASN1 integers are always in big-endian.
        VariableType::Integer { size: 0 }
    }

    fn random_value(size: usize) -> (Vec<u8>, BigUint) {
        // Generate a random big integer but make sure that the MSB is nonzero
        // so that the ASN1 encoder will not shrink its size.
        let mut val = (1..size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
        val.insert(0, 0xff);
        let big_int = BigUint::from_bytes_be(&val);
        (val, big_int)
    }
}

impl Type<String> for String {
    fn variable_type() -> VariableType {
        VariableType::String { size: 0 }
    }

    fn random_value(size: usize) -> (Vec<u8>, String) {
        let bytes = (0..size)
            .map(|_| rand::distributions::Alphanumeric.sample(&mut rand::thread_rng()))
            .collect::<Vec<_>>();
        let string = std::str::from_utf8(&bytes)
            .expect("Alphanumeric returned invalid ASCII characters!")
            .to_string();
        (bytes, string)
    }
}

fn check_conversion(
    source: &VariableType,
    target: VariableType,
    convert: &Option<Conversion>,
    allowed_convert: &Vec<Option<Conversion>>,
) -> Result<VariableType> {
    ensure!(
        allowed_convert.contains(convert),
        "cannot convert from {:?} to {:?} using conversion {:?}, possible conversions are {:?}",
        source,
        target,
        convert,
        allowed_convert
    );
    Ok(target)
}

// Given a source variable type, an optional conversion and a target variable type
// (of unspecified size), return either an error if this conversion does not make
// sense, or return the target variable type with the size that corresponds to the
// input size after conversion.
pub fn convert_type(
    source: &VariableType,
    target: &VariableType,
    convert: &Option<Conversion>,
) -> Result<VariableType> {
    let no_conv = vec![None];
    let endian_conv = vec![Some(Conversion::BigEndian)];
    match (source, target) {
        (_, VariableType::ByteArray { .. }) => {
            // A conversion to a byte array is always possible and does not change
            // the size. No conversion operator allowed.
            check_conversion(
                source,
                VariableType::ByteArray {
                    size: source.size(),
                },
                convert,
                &no_conv,
            )
        }
        (VariableType::ByteArray { size }, VariableType::String { .. }) => {
            // A conversion from a byte array to a string is possible using a lowercase
            // hex conversion. This doubles the size.
            check_conversion(
                source,
                VariableType::String { size: size * 2 },
                convert,
                &vec![Some(Conversion::LowercaseHex)],
            )
        }
        (&VariableType::String { size }, VariableType::String { .. }) => {
            // A conversion to a byte array is always possible and does not change
            // the size. No conversion operator allowed.
            check_conversion(source, VariableType::String { size }, convert, &no_conv)
        }
        (VariableType::Integer { .. }, VariableType::String { .. }) => {
            // Currently not allowed.
            bail!("cannot convert from integer to string")
        }
        (&VariableType::ByteArray { size }, VariableType::Integer { .. }) => {
            // A conversion from a byte array to an integer is possible but must specify how to interpret
            // the original array as an integer.
            check_conversion(
                source,
                VariableType::Integer { size },
                convert,
                &endian_conv,
            )
        }
        (VariableType::String { .. }, VariableType::Integer { .. }) => {
            // Currently not allowed.
            bail!("cannot convert from string to integer")
        }
        (&VariableType::Integer { size }, VariableType::Integer { .. }) => {
            // A conversion is always possible and will handle the difference in endianness.
            check_conversion(source, VariableType::Integer { size }, convert, &no_conv)
        }
    }
}
