// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod bigint;
pub mod bitbang;
pub mod bitfield;
pub mod file;
pub mod hexdump;
pub mod num_de;
pub mod parse_int;
pub mod present;
pub mod printer;
pub mod raw_tty;
pub mod rom_detect;
pub mod serde;
pub mod status;
pub mod testing;
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

/// Create a filename in a temporary directory.
///
/// When running under bazel, the filename will exist in the test's undeclared outputs directory.
pub fn tmpfilename(name: &str) -> String {
    let mut dir = match std::env::var("TEST_UNDECLARED_OUTPUTS_DIR") {
        Ok(name) => std::path::PathBuf::from(name),
        Err(_) => std::env::temp_dir(),
    };
    dir.push(name);
    dir.to_str().unwrap().into()
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
