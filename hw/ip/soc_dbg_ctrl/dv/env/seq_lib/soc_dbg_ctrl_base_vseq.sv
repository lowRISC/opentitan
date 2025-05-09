// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class soc_dbg_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (soc_dbg_ctrl_core_reg_block),
    .CFG_T               (soc_dbg_ctrl_env_cfg),
    .COV_T               (soc_dbg_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (soc_dbg_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(soc_dbg_ctrl_base_vseq)

  soc_dbg_ctrl_jtag_reg_block jtag_ral;

  // Various knobs to enable certain routines
  bit do_soc_dbg_ctrl_init = 1'b1;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void set_handles();
  extern task dut_init(string reset_kind = "HARD");
  extern task soc_dbg_ctrl_init();
endclass : soc_dbg_ctrl_base_vseq


function soc_dbg_ctrl_base_vseq::new(string name="");
  super.new(name);
endfunction : new

function void soc_dbg_ctrl_base_vseq::set_handles();
  super.set_handles();
  `downcast(jtag_ral, cfg.ral_models[cfg.jtag_ral_name]);
endfunction : set_handles

task soc_dbg_ctrl_base_vseq::dut_init(string reset_kind = "HARD");
  // Initialize some of DUT inputs
  cfg.misc_vif.set_soc_dbg_state_blank();
  cfg.misc_vif.set_lc_dft_en_off();
  cfg.misc_vif.set_lc_hw_debug_en_off();
  cfg.misc_vif.set_lc_raw_test_rma_off();
  cfg.misc_vif.init_boot_status();
  cfg.misc_vif.enable_halt_cpu_boot();

  super.dut_init();

  if (do_soc_dbg_ctrl_init) begin
    soc_dbg_ctrl_init();
  end
endtask : dut_init

task soc_dbg_ctrl_base_vseq::soc_dbg_ctrl_init();
  bit [3:0] tmp_core_test;
  bit       tmp_jtag_test;
  csr_rd(.ptr(ral.debug_policy_relocked), .value(tmp_core_test));
  `uvm_info(`gfn, $sformatf("tmp_core_test BEFORE write is %0h", tmp_core_test), UVM_LOW)
  csr_wr(.ptr(ral.debug_policy_relocked), .value(4'hA));
  csr_rd(.ptr(ral.debug_policy_relocked), .value(tmp_core_test));
  `uvm_info(`gfn, $sformatf("tmp_core_test AFTER write is %0h", tmp_core_test), UVM_LOW)

  csr_rd(.ptr(jtag_ral.jtag_control), .value(tmp_jtag_test));
  `uvm_info(`gfn, $sformatf("tmp_jtag_test BEFORE write is %0h", tmp_jtag_test), UVM_LOW)
  csr_wr(.ptr(jtag_ral.jtag_control), .value(1'b1));
  csr_rd(.ptr(jtag_ral.jtag_control), .value(tmp_jtag_test));
  `uvm_info(`gfn, $sformatf("tmp_jtag_test AFTER write is %0h", tmp_jtag_test), UVM_LOW)
endtask : soc_dbg_ctrl_init
