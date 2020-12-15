// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(otp_ctrl_env_cfg),
    .COV_T(otp_ctrl_env_cov)
  );
  `uvm_component_utils(otp_ctrl_virtual_sequencer)

  `uvm_component_new

  push_pull_sequencer#(.DeviceDataWidth(SRAM_DATA_SIZE)) sram_pull_sequencer_h[NumSramKeyReqSlots];
  push_pull_sequencer#(.DeviceDataWidth(OTBN_DATA_SIZE)) otbn_pull_sequencer_h;
  push_pull_sequencer#(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_data_pull_sequencer_h;
  push_pull_sequencer#(.DeviceDataWidth(FLASH_DATA_SIZE)) flash_addr_pull_sequencer_h;
  push_pull_sequencer#(.HostDataWidth(lc_ctrl_pkg::LcTokenWidth)) lc_token_pull_sequencer_h;
  push_pull_sequencer#(.DeviceDataWidth(1), .HostDataWidth(LC_PROG_DATA_SIZE))
                       lc_prog_pull_sequencer_h;
endclass
