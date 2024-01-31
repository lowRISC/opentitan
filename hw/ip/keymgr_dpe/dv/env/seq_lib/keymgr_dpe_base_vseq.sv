// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_dpe_base_vseq extends cip_base_vseq #(
    .RAL_T               (keymgr_dpe_reg_block),
    .CFG_T               (keymgr_dpe_env_cfg),
    .COV_T               (keymgr_dpe_env_cov),
    .VIRTUAL_SEQUENCER_T (keymgr_dpe_virtual_sequencer)
  );
  `uvm_object_utils(keymgr_dpe_base_vseq)

  // various knobs to enable certain routines
  // otp_latched is common for all sequences which extend
  // they will set it when they have successfully called their first
  // advance operation out of reset
  bit otp_latched = 1'b0;
  bit do_keymgr_dpe_init = 1'b1;
  bit do_wait_for_init_done = 1'b1;
  bit seq_check_en = 1'b1;

  // avoid multiple thread accessign this CSR at the same time, which causes UVM_WARNING
  semaphore sema_update_control_csr;

  // do operations at StWorkDpeReset
  rand bit do_op_before_init;
  rand keymgr_dpe_pkg::keymgr_dpe_ops_e gen_operation;
  rand keymgr_pkg::keymgr_key_dest_e key_dest;

  rand bit do_rand_otp_key;
  rand bit do_invalid_otp_key;
  rand keymgr_dpe_pkg::keymgr_dpe_policy_t policy;
  rand keymgr_dpe_pkg::keymgr_dpe_slot_idx_e src_slot;
  rand keymgr_dpe_pkg::keymgr_dpe_slot_idx_e dst_slot;

  // save DUT returned current state here, rather than using it from RAL,
  // it's needed info to predict operation result in seq
  keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e current_state =
    keymgr_dpe_pkg::StWorkDpeReset;

  rand bit is_key_version_err;

  constraint is_key_version_err_c {
    is_key_version_err == 0;
  }

  constraint otp_key_c {
    do_rand_otp_key == 0;
    do_invalid_otp_key == 0;
  }

  constraint gen_operation_c {
    gen_operation inside {
      keymgr_dpe_pkg::OpDpeGenSwOut,
      keymgr_dpe_pkg::OpDpeGenHwOut
    };
  }

  `uvm_object_new

  // callback task before LC enables keymgr
  virtual task pre_start();
    sema_update_control_csr = new(1);
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();

    cfg.keymgr_dpe_vif.update_edn_toleranc_cycs(cfg.edn_clk_freq_mhz, cfg.clk_freq_mhz);
    op_before_enable_keymgr();

    cfg.keymgr_dpe_vif.init(do_rand_otp_key, do_invalid_otp_key);
    delay_after_reset_before_access_csr();

    if (do_keymgr_dpe_init) keymgr_dpe_init();
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
  virtual task keymgr_dpe_init();
    // Any OP except advance at StWorkDpeReset will trigger OP error, test these OPs here
    if (do_op_before_init) begin
      repeat ($urandom_range(1, 5)) begin
        keymgr_dpe_invalid_op_at_reset_state();
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
  endtask : keymgr_dpe_init

  virtual task keymgr_dpe_erase(
      int num_gen_op = $urandom_range(1, 4),
      int num_adv_op = $urandom_range(1, 4),
      bit clr_output = $urandom_range(0, 1),
      bit wait_done = 1
  );
    `uvm_info(`gfn,
      $sformatf("Start keymgr_dpe_erase"), UVM_MEDIUM)

    ral.control_shadowed.operation.set(keymgr_dpe_pkg::OpDpeErase);
    ral.control_shadowed.slot_src_sel.set(src_slot);
    ral.control_shadowed.slot_dst_sel.set(dst_slot);
    csr_update(.csr(ral.control_shadowed));
    csr_wr(.ptr(ral.start), .value(1), .blocking(0));

    if (wait_done)
      wait_op_done();

    if (num_adv_op) begin
      src_slot = dst_slot;
    end

    repeat (num_adv_op) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dst_slot)
      keymgr_dpe_advance(wait_done);
    end

    repeat (num_gen_op) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(is_key_version_err)
      update_key_version();
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gen_operation)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(key_dest)
      keymgr_dpe_generate(.operation(gen_operation), .key_dest(key_dest), .wait_done(wait_done));
      if (clr_output) keymgr_dpe_rd_clr();
    end
  endtask : keymgr_dpe_erase

  virtual task keymgr_dpe_disable(
      int num_gen_op = $urandom_range(1, 4),
      int num_adv_op = $urandom_range(1, 4),
      bit clr_output = $urandom_range(0, 1),
      bit wait_done = 1
  );
    `uvm_info(`gfn,
      $sformatf("Start keymgr_dpe_disable"), UVM_MEDIUM)

    ral.control_shadowed.operation.set(keymgr_dpe_pkg::OpDpeDisable);
    ral.control_shadowed.slot_src_sel.set(src_slot);
    ral.control_shadowed.slot_dst_sel.set(dst_slot);
    csr_update(.csr(ral.control_shadowed));
    csr_wr(.ptr(ral.start), .value(1));

    if (wait_done)
      wait_op_done();

    repeat (num_adv_op) begin
      keymgr_dpe_advance(wait_done);
    end

    repeat (num_gen_op) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(is_key_version_err)
      update_key_version();
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gen_operation)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(key_dest)
      keymgr_dpe_generate(.operation(gen_operation), .key_dest(key_dest), .wait_done(wait_done));
      if (clr_output) keymgr_dpe_rd_clr();
    end
  endtask : keymgr_dpe_disable

  // advance to next state and generate output, clear output
  virtual task keymgr_dpe_operations(bit advance_state = $urandom_range(0, 1),
                                     int num_gen_op    = $urandom_range(1, 4),
                                     bit clr_output    = $urandom_range(0, 1),
                                     bit wait_done     = 1);
    `uvm_info(`gfn,
      $sformatf("Start keymgr_dpe_operations num_gen_op %0d advance_state %0d",
        num_gen_op, advance_state), UVM_MEDIUM)

    if (advance_state) keymgr_dpe_advance(wait_done);

    repeat (num_gen_op) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(is_key_version_err)
      update_key_version();
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(gen_operation)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(key_dest)
      keymgr_dpe_generate(.operation(gen_operation), .key_dest(key_dest), .wait_done(wait_done));
      if (clr_output) keymgr_dpe_rd_clr();
    end
  endtask : keymgr_dpe_operations

  // update key_version to match knob `is_key_version_err` and current_state value
  task update_key_version();
    bit [TL_DW-1:0] key_version_val;
    bit [TL_DW-1:0] max_key_ver_val;

    key_version_val = `gmv(ral.key_version[0]);
    max_key_ver_val = `gmv(ral.max_key_ver_shadowed);

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
    int key_version = `gmv(ral.key_version[0]);
    bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
    logic [2:0] operation = `gmv(ral.control_shadowed.operation);
    keymgr_dpe_pkg::keymgr_dpe_ops_e cast_operation = keymgr_dpe_pkg::keymgr_dpe_ops_e'(operation);
    bit[TL_DW-1:0] rd_val;


    case (operation)
      keymgr_dpe_pkg::OpDpeAdvance: begin
        is_good_op &= !(current_state inside {
          keymgr_dpe_pkg::StWorkDpeInvalid,
          keymgr_dpe_pkg::StWorkDpeDisabled
        });
        if (current_state == keymgr_dpe_pkg::StWorkDpeAvailable) begin
          is_good_op &= cfg.keymgr_dpe_vif.internal_key_slots[src_slot].valid == 1;
          is_good_op &= cfg.keymgr_dpe_vif.internal_key_slots[src_slot].boot_stage <
            (keymgr_dpe_pkg::DpeNumBootStages-1);
          is_good_op &= cfg.keymgr_dpe_vif.internal_key_slots[src_slot].key_policy.allow_child == 1;
          if (cfg.keymgr_dpe_vif.internal_key_slots[src_slot].key_policy.retain_parent == 0) begin
            is_good_op &= (src_slot == dst_slot);
          end
          if (cfg.keymgr_dpe_vif.internal_key_slots[src_slot].key_policy.retain_parent == 1) begin
            is_good_op &= (src_slot != dst_slot);
            is_good_op &= !cfg.keymgr_dpe_vif.internal_key_slots[dst_slot].valid;
          end
        end
        `uvm_info(`gfn, $sformatf("wait_op_done: current_state %s is_good_op %d",
            current_state.name, is_good_op), UVM_MEDIUM)
      end
      keymgr_dpe_pkg::OpDpeGenSwOut,
      keymgr_dpe_pkg::OpDpeGenHwOut: begin
        // generating versioned key's is only valid
        // during available state and it's a good op if
        // max_key_ver <= max_key_version
        is_good_op &= (!(current_state inside {
          keymgr_dpe_pkg::StWorkDpeInvalid,
          keymgr_dpe_pkg::StWorkDpeDisabled,
          keymgr_dpe_pkg::StWorkDpeReset
        })) ? key_version <=
        cfg.keymgr_dpe_vif.internal_key_slots[src_slot].max_key_version : 0;
        is_good_op &= cfg.keymgr_dpe_vif.internal_key_slots[src_slot].valid == 1;
      end
      keymgr_dpe_pkg::OpDpeErase: begin
        is_good_op &= !(current_state inside {
          keymgr_dpe_pkg::StWorkDpeInvalid,
          keymgr_dpe_pkg::StWorkDpeDisabled,
          keymgr_dpe_pkg::StWorkDpeReset
        });
        is_good_op &= cfg.keymgr_dpe_vif.internal_key_slots[dst_slot].valid == 1;
      end
      keymgr_dpe_pkg::OpDpeDisable: begin
        is_good_op = !(current_state inside {
          keymgr_dpe_pkg::StWorkDpeInvalid,
          keymgr_dpe_pkg::StWorkDpeDisabled,
          keymgr_dpe_pkg::StWorkDpeReset
        });
      end
      default: begin
      end
    endcase

    `uvm_info(`gfn, $sformatf({"Wait for operation done in state %0s, operation %0s, ",
                               "src_slot[%0d] = %p, dst_slot[%0d] = %p, good_op %0d"},
                              current_state.name, cast_operation.name,
                              src_slot, cfg.keymgr_dpe_vif.internal_key_slots[src_slot],
                              dst_slot, cfg.keymgr_dpe_vif.internal_key_slots[dst_slot],
                              is_good_op),
              UVM_MEDIUM)

    // wait for status to get out of OpWip and check
    // TODO(#667) - need to restructure SCB so that reading a WIP status doesn't cause error
    // for now set the minimum spinwait_delay_ns to 2 to ensure this false error doesn't happen
    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpWip),
                 .compare_op(CompareOpNe), .spinwait_delay_ns($urandom_range(2, 100)));

    exp_status = is_good_op ? keymgr_pkg::OpDoneSuccess : keymgr_pkg::OpDoneFail;

    // if keymgr_dpe_en is set to off during OP,
    // status is checked in scb. hard to predict the result
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

  virtual task keymgr_dpe_advance(bit wait_done = 1,
                                  int sw_binding = $urandom(),
                                  int max_key_ver = $urandom_range(0,4)
                                );
    keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e exp_next_state = get_next_state(
      current_state, keymgr_dpe_pkg::OpDpeAdvance);
    sema_update_control_csr.get();
    `uvm_info(`gfn, $sformatf("Advance key manager state from %0s slot %0d to %0d",
      current_state.name, src_slot, dst_slot), UVM_MEDIUM)

    ral.control_shadowed.operation.set(keymgr_dpe_pkg::OpDpeAdvance);
    ral.control_shadowed.slot_src_sel.set(src_slot);
    ral.control_shadowed.slot_dst_sel.set(dst_slot);
    csr_wr(.ptr(ral.sw_binding[0]), .value(sw_binding));
    csr_wr(.ptr(ral.max_key_ver_shadowed), .value(max_key_ver));
    ral.slot_policy.exportable.set(policy.exportable);
    ral.slot_policy.allow_child.set(policy.allow_child);
    ral.slot_policy.retain_parent.set(policy.retain_parent);
    csr_update(.csr(ral.slot_policy));
    csr_update(.csr(ral.control_shadowed));
    csr_wr(.ptr(ral.start), .value(1));
    sema_update_control_csr.put();

    if (wait_done) begin
      wait_op_done();
      if (get_check_en()) `DV_CHECK_EQ(current_state, exp_next_state)
      // randomly program to 0, which should not affect anything
      if ($urandom_range(0, 1)) csr_wr(.ptr(ral.start), .value(0));
    end
  endtask : keymgr_dpe_advance

  virtual task keymgr_dpe_generate(
      keymgr_dpe_pkg::keymgr_dpe_ops_e operation,
      keymgr_pkg::keymgr_key_dest_e key_dest,
      bit [31:0] salt = $urandom(),
      int key_version = $urandom_range(1,4),
      bit wait_done = 1
    );
    sema_update_control_csr.get();
    `uvm_info(`gfn,
      $sformatf("Generate key manager output w/operation %s and dest %s",
        operation.name, key_dest.name), UVM_MEDIUM)

    ral.control_shadowed.operation.set(int'(operation));
    ral.control_shadowed.dest_sel.set(int'(key_dest));
    ral.control_shadowed.slot_src_sel.set(src_slot);
    ral.control_shadowed.slot_dst_sel.set(dst_slot);
    csr_wr(.ptr(ral.salt[0]), .value(salt));
    csr_wr(.ptr(ral.key_version[0]), .value(key_version));
    csr_update(.csr(ral.control_shadowed));
    csr_wr(.ptr(ral.start), .value(1));
    sema_update_control_csr.put();
    if (wait_done) wait_op_done();
  endtask : keymgr_dpe_generate

  virtual task keymgr_dpe_rd_clr();
    bit [keymgr_pkg::Shares-1:0][DIGEST_SHARE_WORD_NUM-1:0][TL_DW-1:0] sw_share_output;

    read_sw_shares(sw_share_output);

    // 20% read back to check if they're cleared
    if ($urandom_range(0, 4) == 0) begin
      read_sw_shares(sw_share_output);
      if (get_check_en()) `DV_CHECK_EQ(sw_share_output, '0)
    end
  endtask : keymgr_dpe_rd_clr

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
  virtual task keymgr_dpe_invalid_op_at_reset_state();
    keymgr_dpe_operations(.advance_state(0));
  endtask

  // when reset occurs or keymgr_dpe_en = Off, disable checks in seq and check in scb only
  virtual function bit get_check_en();
    return cfg.keymgr_dpe_vif.get_keymgr_dpe_en() && !cfg.under_reset;
  endfunction

  task wait_and_check_fatal_alert(bit check_invalid_state_enterred = 1);
    // could not accurately predict when first fatal alert happen, so wait for the first fatal
    // alert to trigger
    wait(cfg.m_alert_agent_cfgs["fatal_fault_err"].vif.alert_tx_final.alert_p);
    check_fatal_alert_nonblocking("fatal_fault_err");
    cfg.clk_rst_vif.wait_clks($urandom_range(1, 500));

    if (check_invalid_state_enterred) begin
      csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_dpe_pkg::StWorkDpeInvalid));
    end
  endtask

  virtual task check_after_fi();
    bit issue_adv_or_gen = $urandom;
    // after FI, keymgr should enter StInvalid state immediately
    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_dpe_pkg::StWorkDpeInvalid));
    // issue any operation
    issue_a_random_op(.wait_done(0));
    // waiting for done is called separately as this one expects to be failed
    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpDoneFail),
                 .spinwait_delay_ns($urandom_range(0, 100)));
    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_dpe_pkg::StWorkDpeInvalid));
  endtask

  virtual task issue_a_random_op(bit wait_done);
    bit issue_adv_or_gen = $urandom;
    // issue any operation
    keymgr_dpe_operations(.advance_state(issue_adv_or_gen), .num_gen_op(!issue_adv_or_gen),
                      .wait_done(wait_done));
  endtask
endclass : keymgr_dpe_base_vseq
