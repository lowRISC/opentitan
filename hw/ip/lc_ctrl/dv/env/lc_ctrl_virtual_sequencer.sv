// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(lc_ctrl_env_cfg),
    .COV_T(lc_ctrl_env_cov)
  );
  `uvm_component_utils(lc_ctrl_virtual_sequencer)

  push_pull_sequencer#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
                       .DeviceDataWidth(OTP_PROG_DDATA_WIDTH))    otp_prog_pull_sequencer_h;
  push_pull_sequencer#(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth)) otp_token_pull_sequencer_h;

  alert_esc_sequencer esc_wipe_secrets_sequencer_h;
  alert_esc_sequencer esc_scrap_state_sequencer_h;

  jtag_riscv_sequencer jtag_riscv_sequencer_h;

  `uvm_component_new

endclass
