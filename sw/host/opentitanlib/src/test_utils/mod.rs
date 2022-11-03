// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod bootstrap;
pub mod e2e_command;
pub mod epmp;
pub mod init;
pub mod load_bitstream;
pub mod rpc;
pub mod status;

/// The `execute_test` macro should be used in end-to-end tests to
/// invoke each test from the `main` function.
/// ```
/// fn main() -> Result<()> {
///     // Set up the test environment.
///
///     execute_test!(test_foo, &opts, &stransport);
///     execute_test!(test_bar, &opts, &stransport);
///     execute_test!(test_baz, &opts, &stransport);
///     Ok(())
/// }
/// ```
///
/// The `main` function and each test function should return an `anyhow::Result<()>`.
///
/// The `execute_test` macro will print the standard test header and
/// result footer.  A failed test will abort the program and subsequent tests will
/// not be executed.
#[macro_export]
macro_rules! execute_test {
    ($test:path, $($args:tt)*) => {
        println!("Starting test {}...", stringify!($test));
        let result = $test($($args)*);
        println!("Finished test {}: {:?}", stringify!($test), result);
        let _ = result?;
    };
}
