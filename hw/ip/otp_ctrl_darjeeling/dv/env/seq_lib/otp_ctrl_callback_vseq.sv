// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence hook to attach to otp_ctrl_base_vseq.
class otp_ctrl_callback_vseq extends cip_base_vseq #(
    .RAL_T               (otp_ctrl_core_reg_block),
    .CFG_T               (otp_ctrl_env_cfg),
    .COV_T               (otp_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (otp_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(otp_ctrl_callback_vseq)
  `uvm_object_new

  virtual task dut_init_callback();
    // Do nothing but can be overridden in closed source environment.
  endtask

  virtual task post_otp_pwr_init();
    // Do nothing but can be overridden in closed source environment.
  endtask : post_otp_pwr_init
endclass : otp_ctrl_callback_vseq
