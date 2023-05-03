// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod bootstrap;
pub mod e2e_command;
pub mod epmp;
pub mod extclk;
pub mod gpio;
pub mod init;
pub mod lc_transition;
pub mod load_bitstream;
pub mod load_sram_program;
// The "english breakfast" variant of the chip doesn't have the same
// set of IO and pinmux constants as the "earlgrey" chip.
#[cfg(not(feature = "english_breakfast"))]
pub mod pinmux_config;
pub mod poll;
pub mod rpc;
pub mod spi_passthru;
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
        println!("{}:Starting test {}...", line!(), stringify!($test));
        let result = $test($($args)*);
        println!("{}:Finished test {}: {:?}", line!(), stringify!($test), result);
        let _ = result?;
    };
}
