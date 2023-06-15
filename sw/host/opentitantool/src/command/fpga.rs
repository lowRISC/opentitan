// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use clap::Subcommand;

use opentitanlib::app::command::CommandDispatch;

#[derive(Debug, Subcommand, CommandDispatch)]
/// Commands for interacting with an FPGA instance.
pub enum FpgaCommand {
    LoadBitstream(crate::command::load_bitstream::LoadBitstream),
    ClearBitstream(crate::command::clear_bitstream::ClearBitstream),
    ResetSam3x(crate::command::reset_sam3x::ResetSam3x),
    SetPll(crate::command::set_pll::SetPll),
    UpdateUsrAccess(crate::command::update_usr_access::UpdateUsrAccess),
}
