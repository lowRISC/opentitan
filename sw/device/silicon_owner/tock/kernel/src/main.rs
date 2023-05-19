// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![no_std]
// Disable this attribute when documenting, as a workaround for
// https://github.com/rust-lang/rust/issues/62184.
#![cfg_attr(not(doc), no_main)]

use earlgrey_cw310::setup;
use kernel::capabilities;
use kernel::create_capability;

pub const NUM_PROCS: u8 = 4;

/// Main function.
///
/// This function is called from the arch crate after some very basic RISC-V
/// setup and RAM initialization.
#[no_mangle]
pub unsafe fn main() {
    let (board_kernel, earlgrey_cw310, chip, _peripherals) = setup::setup();

    let main_loop_cap = create_capability!(capabilities::MainLoopCapability);

    board_kernel.kernel_loop(
        earlgrey_cw310,
        chip,
        None::<&kernel::ipc::IPC<NUM_PROCS>>,
        &main_loop_cap,
    );
}
