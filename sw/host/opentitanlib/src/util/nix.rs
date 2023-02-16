// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use nix::errno::Errno;
use nix::libc::{c_int, c_ulong};
use nix::sys::signal::Signal;

#[link(name = "c")]
extern "C" {
    fn prctl(option: c_int, arg2: c_ulong, arg3: c_ulong, arg4: c_ulong, arg5: c_ulong) -> c_int;
}

pub fn request_parent_death_signal(signal: Signal) -> Result<()> {
    const PR_SET_PDEATHSIG: c_int = 1;
    let res = unsafe { prctl(PR_SET_PDEATHSIG, signal as c_ulong, 0, 0, 0) };
    if res != 0 {
        Err(Errno::last()).context("prctl(PR_SET_PDEATHSIG)")
    } else {
        Ok(())
    }
}
