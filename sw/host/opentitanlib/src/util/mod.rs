// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod bigint;
pub mod bitfield;
pub mod file;
pub mod num_de;
pub mod openocd;
pub mod parse_int;
pub mod present;
pub mod printer;
pub mod rom_detect;
pub mod status;
pub mod unknown;
pub mod usb;
pub mod usr_access;
pub mod vmem;
pub mod voltage;

/// The `collection` macro provides syntax for hash and set literals.
#[macro_export]
macro_rules! collection {
    // map-like
    ($($k:expr => $v:expr),* $(,)?) => {{
        use std::iter::{Iterator, IntoIterator};
        Iterator::collect(IntoIterator::into_iter([$(($k, $v),)*]))
    }};

    // set-like
    ($($v:expr),* $(,)?) => {{
        use std::iter::{Iterator, IntoIterator};
        Iterator::collect(IntoIterator::into_iter([$($v),*]))
    }};
}

/// The `testdata` macro can be used in tests to reference testdata directories.
#[macro_export]
#[cfg(test)]
macro_rules! testdata {
    () => {{
        use std::path::PathBuf;
        let mut path = PathBuf::new();
        path.push(file!());
        path.pop();
        path.push("testdata");
        path
    }};
    ($f:expr) => {{
        let mut path = testdata!();
        path.push($f);
        path
    }};
}

#[cfg(test)]
mod test {
    #[test]
    fn test_testdata() {
        assert_eq!(
            testdata!().to_str().unwrap(),
            "sw/host/opentitanlib/src/util/testdata"
        );
        assert_eq!(
            testdata!("my.file").to_str().unwrap(),
            "sw/host/opentitanlib/src/util/testdata/my.file"
        );
    }
}
