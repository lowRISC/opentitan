// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_base_vseq
  extends cip_base_vseq #(.RAL_T               (racl_ctrl_reg_block),
                          .CFG_T               (racl_ctrl_env_cfg),
                          .COV_T               (racl_ctrl_env_cov),
                          .VIRTUAL_SEQUENCER_T (racl_ctrl_virtual_sequencer));

  `uvm_object_utils(racl_ctrl_base_vseq)

  extern function new (string name="");
endclass

function racl_ctrl_base_vseq::new (string name="");
  super.new(name);
endfunction
