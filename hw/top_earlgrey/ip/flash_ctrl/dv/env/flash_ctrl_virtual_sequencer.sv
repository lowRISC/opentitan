// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(flash_ctrl_env_cfg),
    .COV_T(flash_ctrl_env_cov)
  );
  `uvm_component_utils(flash_ctrl_virtual_sequencer)

  tl_sequencer eflash_tl_sequencer_h;

  `uvm_component_new

endclass
