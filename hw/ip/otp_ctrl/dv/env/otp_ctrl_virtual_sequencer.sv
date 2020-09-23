// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(otp_ctrl_env_cfg),
    .COV_T(otp_ctrl_env_cov)
  );
  `uvm_component_utils(otp_ctrl_virtual_sequencer)


  `uvm_component_new

endclass
