// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_base_vseq extends cip_base_vseq #(
    .RAL_T               (keymgr_reg_block),
    .CFG_T               (keymgr_env_cfg),
    .COV_T               (keymgr_env_cov),
    .VIRTUAL_SEQUENCER_T (keymgr_virtual_sequencer)
  );
  `uvm_object_utils(keymgr_base_vseq)

  // various knobs to enable certain routines
  bit do_keymgr_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_keymgr_init) keymgr_init();
  endtask

  virtual task dut_shutdown();
    // check for pending keymgr operations and wait for them to complete
    // TODO
  endtask

  // setup basic keymgr features
  virtual task keymgr_init();
    `uvm_info(`gfn, "Initializating key manager", UVM_LOW)
    ral.control.init.set(1'b1);
    csr_update(.csr(ral.control));
    csr_spinwait(.ptr(ral.working_state), .exp_data(keymgr_pkg::StInit));
  endtask // keymgr_init

  virtual task keymgr_advance();
    bit [3:0] current_state;
    `uvm_info(`gfn, "Advance key manager state", UVM_LOW)
    ral.control.start.set(1'b1);
    ral.control.operation.set(keymgr_pkg::OpAdvance);
    csr_update(.csr(ral.control));

    csr_rd(.ptr(ral.working_state), .value(current_state));
    if (current_state < keymgr_pkg::StInit ||
      current_state == keymgr_pkg::StDisabled) begin
      csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpDoneFail));
    end else begin
      csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpDoneSuccess));
    end

  endtask // keymgr_advance


  // by default generate for software
  virtual task keymgr_generate(bit Identity=0);
    bit [2:0] operation;
    bit [3:0] current_state;

    `uvm_info(`gfn, "Generate key manager output", UVM_LOW)
    ral.control.start.set(1'b1);

    if (Identity) begin
      operation = keymgr_pkg::OpGenId;
    end else begin
      operation = keymgr_pkg::OpGenSwOut;
    end
    ral.control.operation.set(operation);
    csr_update(.csr(ral.control));

    csr_rd(.ptr(ral.working_state), .value(current_state));
    if (current_state < keymgr_pkg::StInit ||
      current_state == keymgr_pkg::StDisabled) begin
      csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpDoneFail));
    end else begin
      csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpDoneSuccess));
    end
  endtask // keymgr_generate


  virtual task keymgr_rd_clr();
    bit [31:0] value[8];
    `uvm_info(`gfn, "Read generated output", UVM_LOW)

    // read each one out and print it out (nothing to compare it against right now)
    // after reading, the outputs should clear
    csr_rd(.ptr(ral.sw_share0_output_0), .value(value[0]));
    csr_rd(.ptr(ral.sw_share0_output_1), .value(value[1]));
    csr_rd(.ptr(ral.sw_share0_output_2), .value(value[2]));
    csr_rd(.ptr(ral.sw_share0_output_3), .value(value[3]));
    csr_rd(.ptr(ral.sw_share0_output_4), .value(value[4]));
    csr_rd(.ptr(ral.sw_share0_output_5), .value(value[5]));
    csr_rd(.ptr(ral.sw_share0_output_6), .value(value[6]));
    csr_rd(.ptr(ral.sw_share0_output_7), .value(value[7]));

    for (int i = 0; i < 8; i++) begin
      `uvm_info(`gfn, $sformatf("Generated output %0d: 0x%0h", i, value[i]), UVM_LOW)
    end

    csr_rd_check(.ptr(ral.sw_share0_output_0), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_1), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_2), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_3), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_4), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_5), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_6), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_7), .compare_value('0));

  endtask // keymgr_rd_clr



endclass : keymgr_base_vseq
