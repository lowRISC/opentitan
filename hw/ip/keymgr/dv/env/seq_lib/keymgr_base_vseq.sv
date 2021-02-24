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
  bit do_wait_for_init_done = 1'b1;
  bit do_reset_at_end_of_seq = 1'b0;
  bit seq_check_en = 1'b1;

  // do operations at StReset
  rand bit do_op_before_init;
  rand keymgr_pkg::keymgr_ops_e gen_operation;

  // save DUT returned current state here, rather than using it from RAL, it's needed info to
  // predict operation result in seq
  keymgr_pkg::keymgr_working_state_e current_state = keymgr_pkg::StReset;

  rand bit is_key_version_err;

  constraint is_key_version_err_c {
    is_key_version_err == 0;
  }

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    cfg.keymgr_vif.init();

    delay_after_reset_before_access_csr();

    if (do_keymgr_init) keymgr_init();
  endtask

  virtual task delay_after_reset_before_access_csr();
    // Add 2 cycles for design to synchronize life cycle value from async domain to update cfg_en
    // otherwise, some register programming will be gated
    cfg.clk_rst_vif.wait_clks(2);
  endtask

  virtual task dut_shutdown();
    // check for pending keymgr operations and wait for them to complete
    // TODO
  endtask

  // setup basic keymgr features
  virtual task keymgr_init();
    // Any OP except advance at StReset will trigger OP error, test these OPs here
    if (do_op_before_init) begin
      repeat ($urandom_range(1, 5)) begin
        keymgr_invalid_op_at_reset_state();
      end
    end

    `uvm_info(`gfn, "Initializating key manager", UVM_MEDIUM)

    `DV_CHECK_RANDOMIZE_FATAL(ral.intr_enable)
    csr_update(.csr(ral.intr_enable));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.reseed_interval.val,
                                   value dist {[50:100]   :/ 1,
                                               [101:1000] :/ 1,
                                               [1001:$]   :/ 1};)
    csr_update(.csr(ral.reseed_interval));
  endtask : keymgr_init

  // advance to next state and generate output, clear output
  virtual task keymgr_operations(bit advance_state = $urandom_range(0, 1),
                                 int num_gen_op    = $urandom_range(1, 4),
                                 bit clr_output    = $urandom_range(0, 1),
                                 bit wait_done     = 1);
    `uvm_info(`gfn, "Start keymgr_operations", UVM_MEDIUM)

    if (advance_state) keymgr_advance(wait_done);

    repeat (num_gen_op) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(is_key_version_err)
      update_key_version();

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gen_operation)
      keymgr_generate(.operation(gen_operation), .wait_done(wait_done));
      if (clr_output) keymgr_rd_clr();
    end
  endtask : keymgr_operations

  // update key_version to match knob `is_key_version_err` and current_state value
  task update_key_version();
    bit [TL_DW-1:0] key_version_val;
    bit [TL_DW-1:0] max_creator_key_ver_val;
    bit [TL_DW-1:0] max_owner_int_key_ver_val;
    bit [TL_DW-1:0] max_owner_key_ver_val;
    bit [TL_DW-1:0] max_key_ver_val;

    key_version_val           = `gmv(ral.key_version);
    max_creator_key_ver_val   = `gmv(ral.max_creator_key_ver);
    max_owner_int_key_ver_val = `gmv(ral.max_owner_int_key_ver);
    max_owner_key_ver_val     = `gmv(ral.max_owner_key_ver);
    max_key_ver_val = (current_state == keymgr_pkg::StCreatorRootKey)
        ? max_creator_key_ver_val : (current_state == keymgr_pkg::StOwnerIntKey)
        ? max_owner_int_key_ver_val : (current_state == keymgr_pkg::StOwnerKey)
        ? max_owner_key_ver_val : 0;

    // if current key_version already match to what we need, return without updating it
    if (is_key_version_err && key_version_val > max_key_ver_val ||
        !is_key_version_err && key_version_val <= max_key_ver_val) begin
      return;
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(key_version_val,
                                       if (is_key_version_err) {
                                         max_key_ver_val != '1 -> key_version_val > max_key_ver_val;
                                       } else {
                                         key_version_val <= max_key_ver_val;
                                       })
    ral.key_version.set(key_version_val);
    csr_update(ral.key_version);
  endtask

  virtual task wait_op_done();
    keymgr_pkg::keymgr_op_status_e exp_status;
    bit is_good_op = 1;
    int key_verion = `gmv(ral.key_version);
    keymgr_pkg::keymgr_ops_e operation = `gmv(ral.control.operation);
    bit[TL_DW-1:0] rd_val;

    if (operation inside {keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut}) begin
      // only when it's in 3 working state and key_verion less than max version
      case (current_state)
        keymgr_pkg::StCreatorRootKey: begin
          is_good_op = key_verion <= ral.max_creator_key_ver.get_mirrored_value();
        end
        keymgr_pkg::StOwnerIntKey: begin
          is_good_op = key_verion <= ral.max_owner_int_key_ver.get_mirrored_value();
        end
        keymgr_pkg::StOwnerKey: begin
          is_good_op = key_verion <= ral.max_owner_key_ver.get_mirrored_value();
        end
        default: is_good_op = 0;
      endcase
    end else if (operation == keymgr_pkg::OpGenId) begin
      is_good_op = current_state inside {keymgr_pkg::StCreatorRootKey, keymgr_pkg::StOwnerIntKey,
                                         keymgr_pkg::StOwnerKey};
    end else if (operation == keymgr_pkg::OpAdvance) begin
      is_good_op = current_state != keymgr_pkg::StDisabled;
    end else begin
      is_good_op = !(current_state inside {keymgr_pkg::StReset, keymgr_pkg::StDisabled});
    end
    `uvm_info(`gfn, $sformatf("Wait for operation done in state %0s, operation %0s, good_op %0d",
                              current_state.name, operation.name, is_good_op), UVM_MEDIUM)

    // wait for status to get out of OpWip and check
    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpWip),
                 .compare_op(CompareOpNe), .spinwait_delay_ns($urandom_range(0, 100)));

    exp_status = is_good_op ? keymgr_pkg::OpDoneSuccess : keymgr_pkg::OpDoneFail;

    // if keymgr_en is set to off during OP, status is checked in scb. hard to predict the result
    // in seq
    if (get_check_en()) begin
      `DV_CHECK_EQ(`gmv(ral.op_status.status), exp_status)
      // check and clear interrupt
      check_interrupts(.interrupts(1 << IntrOpDone), .check_set(1));
    end

    read_current_state();

    // check for chech in scb and clear err_code
    csr_rd(.ptr(ral.err_code), .value(rd_val));
    if (rd_val != 0) begin
      csr_wr(.csr(ral.err_code), .value(rd_val));
    end
  endtask : wait_op_done

  virtual task read_current_state();
    bit [TL_DW-1:0] rdata;

    csr_rd(.ptr(ral.working_state), .value(rdata));
    if (!cfg.under_reset) begin
      `downcast(current_state, rdata)
      `uvm_info(`gfn, $sformatf("Current state %0s", current_state.name), UVM_MEDIUM)
    end
  endtask : read_current_state

  virtual task keymgr_advance(bit wait_done = 1);
    keymgr_pkg::keymgr_working_state_e exp_next_state = get_next_state(current_state);
    `uvm_info(`gfn, $sformatf("Advance key manager state from %0s", current_state.name), UVM_MEDIUM)
    ral.control.start.set(1'b1);
    ral.control.operation.set(keymgr_pkg::OpAdvance);
    csr_update(.csr(ral.control));

    if (wait_done) begin
      wait_op_done();
      if (get_check_en()) `DV_CHECK_EQ(current_state, exp_next_state)
    end
  endtask : keymgr_advance

  // by default generate for software
  virtual task keymgr_generate(keymgr_pkg::keymgr_ops_e operation, bit wait_done = 1);
    `uvm_info(`gfn, "Generate key manager output", UVM_MEDIUM)

    ral.control.start.set(1'b1);
    ral.control.operation.set(int'(operation));
    // TODO, test KMAC interface only since the other interface may be removed later
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.control.dest_sel,
                                   value inside {keymgr_pkg::None, keymgr_pkg::Kmac};);
    csr_update(.csr(ral.control));
    ral.control.start.set(1'b0);

    if (wait_done) wait_op_done();
  endtask : keymgr_generate

  virtual task keymgr_rd_clr();
    bit [keymgr_pkg::Shares-1:0][DIGEST_SHARE_WORD_NUM-1:0][TL_DW-1:0] sw_share_output;
    `uvm_info(`gfn, "Read generated output", UVM_MEDIUM)

    // read each one out and print it out (nothing to compare it against right now)
    // after reading, the outputs should clear
    foreach (sw_share_output[i, j]) begin
      string csr_name = $sformatf("sw_share%0d_output_%0d", i, j);
      uvm_reg csr = ral.get_reg_by_name(csr_name);

      csr_rd(.ptr(csr), .value(sw_share_output[i][j]));
      `uvm_info(`gfn, $sformatf("%0s: 0x%0h", csr_name, sw_share_output[i][j]), UVM_HIGH)
    end

    // 20% read back to check if they're cleared
    if ($urandom_range(0, 4) == 0) begin
      foreach (sw_share_output[i, j]) begin
        bit [TL_DW-1:0] rd_val;
        string csr_name = $sformatf("sw_share%0d_output_%0d", i, j);
        uvm_reg csr = ral.get_reg_by_name(csr_name);

        csr_rd(.ptr(csr), .value(rd_val));
        if (get_check_en()) `DV_CHECK_EQ(rd_val, '0)
      end
    end
  endtask : keymgr_rd_clr

  // issue any invalid operation at reset state to trigger op error
  virtual task keymgr_invalid_op_at_reset_state();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.control,
                                   operation.value != keymgr_pkg::OpAdvance;)

    `uvm_info(`gfn, $sformatf("Issuing OP: %0d at state %0s",
                              ral.control.operation.get(), current_state), UVM_MEDIUM)
    csr_update(.csr(ral.control));
    if (ral.control.start.get()) wait_op_done();
  endtask

  // when reset occurs or keymgr_en = Off, disable checks in seq and check in scb only
  virtual function bit get_check_en();
    return cfg.keymgr_vif.keymgr_en == lc_ctrl_pkg::On && !cfg.under_reset;
  endfunction

  task post_start();
    super.post_start();

    // If fatal alert will be triggered in this seq, issue reset if reset is allowed, otherwise,
    // reset will be called in upper vseq
    if (do_reset_at_end_of_seq) begin
      #10_000ns;
      if (do_apply_reset) apply_reset();
    end
  endtask

endclass : keymgr_base_vseq
