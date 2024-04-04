// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_main]
#![no_std]
use core::fmt::Write;
use libtock::console::Console;
use libtock::runtime::{set_main, stack_size};

set_main!(main);
stack_size!(0x200);

fn main() {
    write!(Console::writer(), "Hello world!\r\n").unwrap();
    // opentitan_functest's default test harness looks for `PASS` or `FAIL` in
    // the test output to determine the test result.
    write!(Console::writer(), "PASS!\r\n").unwrap();
}
