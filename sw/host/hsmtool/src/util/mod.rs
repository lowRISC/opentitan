// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod attribute;
pub mod ef;
pub mod escape;
pub mod helper;
pub mod key;
pub mod secret;
pub mod signing;
pub mod wrap;

/// The `testdata` function can be used in tests to reference testdata directories.
#[cfg(test)]
pub fn testdata(test: &str) -> std::path::PathBuf {
    let mut path: std::path::PathBuf = std::env::var_os("TESTDATA").unwrap().into();
    // TESTDATA points an arbitrary test, remove two levels to get the directory.
    path.pop();
    path.pop();
    path.push(test);
    path
}
