// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(rram_ctrl_env_cfg),
    .COV_T(rram_ctrl_env_cov)
  );
  `uvm_component_utils(rram_ctrl_virtual_sequencer)

  tl_csr_sequencer tl_csr_sequencer_h;
  tl_host_sequencer tl_host_sequencer_h;
  tl_prim_sequencer tl_prim_sequencer_h;

  `uvm_component_new

endclass
