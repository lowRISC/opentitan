// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_base_vseq extends cip_base_vseq #(
    .RAL_T               (ac_range_check_reg_block),
    .CFG_T               (ac_range_check_env_cfg),
    .COV_T               (ac_range_check_env_cov),
    .VIRTUAL_SEQUENCER_T (ac_range_check_virtual_sequencer)
  );
  `uvm_object_utils(ac_range_check_base_vseq)

  // Various knobs to enable certain routines
  bit do_ac_range_check_init = 1'b1;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern task dut_init(string reset_kind = "HARD");
  extern task ac_range_check_init();
endclass : ac_range_check_base_vseq


function ac_range_check_base_vseq::new(string name="");
  super.new(name);
endfunction : new

task ac_range_check_base_vseq::dut_init(string reset_kind = "HARD");
  super.dut_init();
  if (do_ac_range_check_init) begin
    ac_range_check_init();
  end
endtask : dut_init

task ac_range_check_base_vseq::ac_range_check_init();
  `uvm_error(`gfn, "FIXME")
endtask : ac_range_check_init
