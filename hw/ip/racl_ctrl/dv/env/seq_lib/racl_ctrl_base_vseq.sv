// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_base_vseq
  extends cip_base_vseq #(.RAL_T               (racl_ctrl_reg_block),
                          .CFG_T               (racl_ctrl_env_cfg),
                          .COV_T               (racl_ctrl_env_cov),
                          .VIRTUAL_SEQUENCER_T (racl_ctrl_virtual_sequencer));

  `uvm_object_utils(racl_ctrl_base_vseq)

  // Handles to the sequencers for the internal and external error log agents
  racl_error_log_sequencer internal_error_log_sequencer_h;
  racl_error_log_sequencer external_error_log_sequencer_h;

  extern function new (string name="");
  extern task body();
endclass

function racl_ctrl_base_vseq::new (string name="");
  super.new(name);
endfunction

task racl_ctrl_base_vseq::body();

endtask
