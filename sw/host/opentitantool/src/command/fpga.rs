// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;

#[derive(Debug, StructOpt, CommandDispatch)]
/// Commands for interacting with an FPGA instance.
pub enum FpgaCommand {
    LoadBitstream(crate::command::load_bitstream::LoadBitstream),
    Reset(crate::command::fpga_reset::FpgaReset),
    SetPll(crate::command::set_pll::SetPll),
}
