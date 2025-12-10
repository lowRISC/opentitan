// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (rram_ctrl_core_reg_block),
    .CFG_T               (rram_ctrl_env_cfg),
    .COV_T               (rram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (rram_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(rram_ctrl_base_vseq)

  rram_macro_prim_reg_block prim_ral;

  // Various knobs to enable certain routines
  bit do_rram_ctrl_init = 1'b1;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void set_handles();
  extern task dut_init(string reset_kind = "HARD");
  extern task rram_ctrl_init();
endclass : rram_ctrl_base_vseq


function rram_ctrl_base_vseq::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_base_vseq::set_handles();
  super.set_handles();
  `downcast(prim_ral, cfg.ral_models[cfg.prim_ral_name]);
endfunction : set_handles

task rram_ctrl_base_vseq::dut_init(string reset_kind = "HARD");
  // Initialize some of DUT inputs
  // TODO
  // cfg.misc_vif.<my_function/my_task>

  super.dut_init();

  if (do_rram_ctrl_init) begin
    rram_ctrl_init();
  end
endtask : dut_init

task rram_ctrl_base_vseq::rram_ctrl_init();
  // TODO
  #1ms;
endtask : rram_ctrl_init
