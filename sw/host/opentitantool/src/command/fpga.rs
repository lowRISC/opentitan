// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use clap::Subcommand;

use opentitanlib::app::command::CommandDispatch;

#[derive(Debug, Subcommand, CommandDispatch)]
/// Commands for interacting with an FPGA instance.
pub enum FpgaCommand {
    LoadBitstream(crate::command::load_bitstream::LoadBitstream),
    ClearBitstream(crate::command::clear_bitstream::ClearBitstream),
    GetSam3xFwVersion(crate::command::sam3x::GetFwVersion),
    ResetSam3x(crate::command::sam3x::Reset),
    SetPll(crate::command::set_pll::SetPll),
    UpdateUsrAccess(crate::command::update_usr_access::UpdateUsrAccess),
}
