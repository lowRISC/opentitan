// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod attribute;
pub mod ef;
pub mod escape;
pub mod helper;
pub mod key;
pub mod signing;

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
            "sw/host/hsmtool/src/util/testdata"
        );
        assert_eq!(
            testdata!("my.file").to_str().unwrap(),
            "sw/host/hsmtool/src/util/testdata/my.file"
        );
    }
}
