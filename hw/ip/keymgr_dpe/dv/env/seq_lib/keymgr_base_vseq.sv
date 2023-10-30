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
  bit seq_check_en = 1'b1;

  // avoid multiple thread accessign this CSR at the same time, which causes UVM_WARNING
  semaphore sema_update_control_csr;

  // do operations at StReset
  rand bit do_op_before_init;
  rand keymgr_pkg::keymgr_ops_e gen_operation;
  rand keymgr_pkg::keymgr_key_dest_e key_dest;

  rand bit do_rand_otp_key;
  rand bit do_invalid_otp_key;

  // save DUT returned current state here, rather than using it from RAL, it's needed info to
  // predict operation result in seq
  keymgr_pkg::keymgr_working_state_e current_state = keymgr_pkg::StReset;

  rand bit is_key_version_err;

  constraint is_key_version_err_c {
    is_key_version_err == 0;
  }

  constraint otp_key_c {
    do_rand_otp_key == 0;
    do_invalid_otp_key == 0;
  }

  constraint gen_operation_c {
    gen_operation inside {keymgr_pkg::OpGenId, keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut};
  }

  `uvm_object_new

  // callback task before LC enables keymgr
  virtual task pre_start();
    sema_update_control_csr = new(1);
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();

    cfg.keymgr_vif.update_edn_toleranc_cycs(cfg.edn_clk_freq_mhz, cfg.clk_freq_mhz);
    op_before_enable_keymgr();

    cfg.keymgr_vif.init(do_rand_otp_key, do_invalid_otp_key);
    delay_after_reset_before_access_csr();

    if (do_keymgr_init) keymgr_init();
  endtask

  // callback task before LC enables keymgr
  virtual task op_before_enable_keymgr();
  endtask

  virtual task delay_after_reset_before_access_csr();
    bit cdc_instrumentation_enabled;
    void'($value$plusargs("cdc_instrumentation_enabled=%d", cdc_instrumentation_enabled));

    // Add 2 cycles for design to synchronize life cycle value from async domain to update cfg_en
    // otherwise, some register programming will be gated
    cfg.clk_rst_vif.wait_clks(2);

    if (cdc_instrumentation_enabled) cfg.clk_rst_vif.wait_clks(1);
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
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.reseed_interval_shadowed.val,
                                   value dist {[50:100]   :/ 1,
                                               [101:1000] :/ 1,
                                               [1001:$]   :/ 1};)
    csr_update(.csr(ral.reseed_interval_shadowed));
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
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(key_dest)
      keymgr_generate(.operation(gen_operation), .key_dest(key_dest), .wait_done(wait_done));
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

    key_version_val           = `gmv(ral.key_version[0]);
    max_creator_key_ver_val   = `gmv(ral.max_creator_key_ver_shadowed);
    max_owner_int_key_ver_val = `gmv(ral.max_owner_int_key_ver_shadowed);
    max_owner_key_ver_val     = `gmv(ral.max_owner_key_ver_shadowed);
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
                                         key_version_val == max_key_ver_val dist {0 :/ 3, 1 :/ 1};
                                       })
    ral.key_version[0].set(key_version_val);
    csr_update(ral.key_version[0]);
  endtask

  virtual task wait_op_done();
    keymgr_pkg::keymgr_op_status_e exp_status;
    bit is_good_op = 1;
    int key_verion = `gmv(ral.key_version[0]);
    logic [2:0] operation = `gmv(ral.control_shadowed.operation);
    keymgr_pkg::keymgr_ops_e cast_operation = keymgr_pkg::keymgr_ops_e'(operation);
    bit[TL_DW-1:0] rd_val;

    if (operation inside {keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut}) begin
      // only when it's in 3 working state and key_verion less than max version
      case (current_state)
        keymgr_pkg::StCreatorRootKey: begin
          is_good_op = key_verion <= ral.max_creator_key_ver_shadowed.get_mirrored_value();
        end
        keymgr_pkg::StOwnerIntKey: begin
          is_good_op = key_verion <= ral.max_owner_int_key_ver_shadowed.get_mirrored_value();
        end
        keymgr_pkg::StOwnerKey: begin
          is_good_op = key_verion <= ral.max_owner_key_ver_shadowed.get_mirrored_value();
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
                              current_state.name, cast_operation.name, is_good_op), UVM_MEDIUM)

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

    // check err_code in scb and clear err_code
    csr_rd(.ptr(ral.err_code), .value(rd_val));
    if (rd_val != 0) begin
      csr_wr(.ptr(ral.err_code), .value(rd_val));
    end
    // check fault_status
    csr_rd(.ptr(ral.fault_status), .value(rd_val));
    // Do a dummy write to RO register
    if (rd_val != 0 && $urandom_range(0, 1)) begin
      csr_wr(.ptr(ral.fault_status), .value($urandom));
    end
    // read and clear interrupt
    csr_rd(.ptr(ral.intr_state), .value(rd_val));
    if (rd_val != 0) begin
      csr_wr(.ptr(ral.intr_state), .value(rd_val));
    end
    // read and clear debug CSRs, check is done in scb
    csr_rd(.ptr(ral.debug), .value(rd_val));
    if (rd_val != 0) begin
      // this CSR is w0c
      csr_wr(.ptr(ral.debug), .value(~rd_val));
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
    sema_update_control_csr.get();
    `uvm_info(`gfn, $sformatf("Advance key manager state from %0s", current_state.name), UVM_MEDIUM)
    ral.control_shadowed.operation.set(keymgr_pkg::OpAdvance);
    csr_update(.csr(ral.control_shadowed));
    csr_wr(.ptr(ral.start), .value(1));
    sema_update_control_csr.put();

    if (wait_done) begin
      wait_op_done();
      if (get_check_en()) `DV_CHECK_EQ(current_state, exp_next_state)
      // randomly program to 0, which should not affect anything
      if ($urandom_range(0, 1)) csr_wr(.ptr(ral.start), .value(0));
    end
  endtask : keymgr_advance

  // by default generate for software
  virtual task keymgr_generate(keymgr_pkg::keymgr_ops_e operation,
                               keymgr_pkg::keymgr_key_dest_e key_dest,
                               bit wait_done = 1);
    sema_update_control_csr.get();
    `uvm_info(`gfn, "Generate key manager output", UVM_MEDIUM)

    ral.control_shadowed.operation.set(int'(operation));
    `DV_CHECK_RANDOMIZE_FATAL(ral.control_shadowed.cdi_sel)
    ral.control_shadowed.dest_sel.set(int'(key_dest));
    csr_update(.csr(ral.control_shadowed));
    sema_update_control_csr.put();
    csr_wr(.ptr(ral.start), .value(1));

    if (wait_done) wait_op_done();
  endtask : keymgr_generate

  virtual task keymgr_rd_clr();
    bit [keymgr_pkg::Shares-1:0][DIGEST_SHARE_WORD_NUM-1:0][TL_DW-1:0] sw_share_output;

    read_sw_shares(sw_share_output);

    // 20% read back to check if they're cleared
    if ($urandom_range(0, 4) == 0) begin
      read_sw_shares(sw_share_output);
      if (get_check_en()) `DV_CHECK_EQ(sw_share_output, '0)
    end
  endtask : keymgr_rd_clr

  virtual task read_sw_shares(
        output bit [keymgr_pkg::Shares-1:0][DIGEST_SHARE_WORD_NUM-1:0][TL_DW-1:0] sw_share_output);
    `uvm_info(`gfn, "Read generated output", UVM_MEDIUM)

    // read each one out and print it out (nothing to compare it against right now)
    // after reading, the outputs should clear
    foreach (sw_share_output[i, j]) begin
      string csr_name = $sformatf("sw_share%0d_output_%0d", i, j);
      uvm_reg csr = ral.get_reg_by_name(csr_name);

      csr_rd(.ptr(csr), .value(sw_share_output[i][j]));
      `uvm_info(`gfn, $sformatf("%0s: 0x%0h", csr_name, sw_share_output[i][j]), UVM_HIGH)
    end
  endtask : read_sw_shares

  // issue any invalid operation at reset state to trigger op error
  virtual task keymgr_invalid_op_at_reset_state();
    keymgr_operations(.advance_state(0));
  endtask

  // when reset occurs or keymgr_en = Off, disable checks in seq and check in scb only
  virtual function bit get_check_en();
    return cfg.keymgr_vif.get_keymgr_en() && !cfg.under_reset;
  endfunction

  task wait_and_check_fatal_alert(bit check_invalid_state_enterred = 1);
    // could not accurately predict when first fatal alert happen, so wait for the first fatal
    // alert to trigger
    wait(cfg.m_alert_agent_cfgs["fatal_fault_err"].vif.alert_tx_final.alert_p);
    check_fatal_alert_nonblocking("fatal_fault_err");
    cfg.clk_rst_vif.wait_clks($urandom_range(1, 500));

    if (check_invalid_state_enterred) begin
      csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_pkg::StInvalid));
    end
  endtask

  virtual task check_after_fi();
    bit issue_adv_or_gen = $urandom;
    // after FI, keymgr should enter StInvalid state immediately
    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_pkg::StInvalid));
    // issue any operation
    issue_a_random_op(.wait_done(0));
    // waiting for done is called separately as this one expects to be failed
    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpDoneFail),
                 .spinwait_delay_ns($urandom_range(0, 100)));
    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_pkg::StInvalid));
  endtask

  virtual task issue_a_random_op(bit wait_done);
    bit issue_adv_or_gen = $urandom;
    // issue any operation
    keymgr_operations(.advance_state(issue_adv_or_gen), .num_gen_op(!issue_adv_or_gen),
                      .wait_done(wait_done));
  endtask
endclass : keymgr_base_vseq
