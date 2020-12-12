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

  // do operations at StReset
  rand bit do_op_before_init;
  rand keymgr_pkg::keymgr_ops_e op_before_init;

  constraint invalid_ops_before_init {
    op_before_init inside {ILLEGAL_OPS_B4_INIT};
  }

  // save DUT returned current state here, rather than using it from RAL, it's needed info to
  // predict operation result in seq
  keymgr_pkg::keymgr_working_state_e current_state;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    cfg.keymgr_vif.init();
    if (do_keymgr_init) keymgr_init();
  endtask

  virtual task dut_shutdown();
    // check for pending keymgr operations and wait for them to complete
    // TODO
  endtask

  // setup basic keymgr features
  virtual task keymgr_init();
    current_state = keymgr_pkg::StReset;

    // Any OP at StReset will trigger OP error. There are 5 kinds of OPs
    // Also test both start and init set to 1, which triggers OP error as well
    if (do_op_before_init) begin
      repeat ($urandom_range(1, 5)) keymgr_random_op(.start(1), .init(1));
    end

    `uvm_info(`gfn, "Initializating key manager", UVM_MEDIUM)

    `DV_CHECK_RANDOMIZE_FATAL(ral.intr_enable)
    csr_update(.csr(ral.intr_enable));

    ral.control.operation.set(keymgr_pkg::OpAdvance);
    ral.control.start.set(1'b1);
    csr_update(.csr(ral.control));
    // manually clear here since ral is not aware this bet is self-clearing
    ral.control.start.set(1'b0);

    // Add 1 cycle delay for working_state to be updated, which makes scb less complicated
    cfg.clk_rst_vif.wait_clks(1);

    if (do_wait_for_init_done) begin
      csr_spinwait(.ptr(ral.working_state), .exp_data(keymgr_pkg::StInit));
      current_state = keymgr_pkg::StInit;
    end
  endtask : keymgr_init

  // advance to next state and generate output, clear output
  virtual task keymgr_operations(bit advance_state = $urandom_range(0, 1),
                                 int num_gen_op    = $urandom_range(1, 4),
                                 bit clr_output    = $urandom_range(0, 1),
                                 bit wait_done     = 1);
    `uvm_info(`gfn, "Start keymgr_operations", UVM_MEDIUM)

    if (advance_state) keymgr_advance(wait_done);

    repeat (num_gen_op) begin
      keymgr_generate(.identity($urandom_range(0, 1)), .wait_done(wait_done));
      if (clr_output) keymgr_rd_clr();
    end
  endtask : keymgr_operations

  virtual task wait_op_done(bit is_gen_output);
    keymgr_pkg::keymgr_op_status_e exp_status;
    bit is_good_op = 1;
    int key_verion = ral.key_version.get_mirrored_value();
    bit intr_err_exp;

    if (is_gen_output) begin
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
    end else begin
      is_good_op = current_state inside {LIST_OF_NORMAL_STATES};
    end
    `uvm_info(`gfn, $sformatf("Wait for operation done in state %0s, gen_out %0d, good_op %0d",
                              current_state.name, is_gen_output, is_good_op), UVM_MEDIUM)

    // wait for status to get out of OpWip and check
    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpWip),
                 .compare_op(CompareOpNe), .spinwait_delay_ns($urandom_range(0, 100)));
    exp_status = is_good_op ? keymgr_pkg::OpDoneSuccess : keymgr_pkg::OpDoneFail;
    `DV_CHECK_EQ(ral.op_status.status.get_mirrored_value(), exp_status)

    read_current_state();

    // check and clear interrupt
    check_interrupts(.interrupts(1 << IntrOpDone), .check_set(1));
    check_interrupts(.interrupts(1 << IntrErr), .check_set(!is_good_op));

    // check and clear err_code
    csr_rd_check(.ptr(ral.err_code.invalid_op), .compare_value(!is_good_op));
    if (!is_good_op) begin
      bit [TL_DW-1:0] err_code_wdata;
      err_code_wdata = get_csr_val_with_updated_field(.field(ral.err_code.invalid_op),
                                                      .csr_value(err_code_wdata),
                                                      .field_value(1));
      csr_wr(.csr(ral.err_code), .value(err_code_wdata));
    end
  endtask : wait_op_done

  virtual task read_current_state();
    bit [TL_DW-1:0] rdata;

    csr_rd(.ptr(ral.working_state), .value(rdata));
    `downcast(current_state, rdata)
    `uvm_info(`gfn, $sformatf("Current state %0s", current_state.name), UVM_MEDIUM)
  endtask : read_current_state

  virtual task keymgr_advance(bit wait_done = 1);
    keymgr_pkg::keymgr_working_state_e exp_next_state = get_next_state(current_state);
    `uvm_info(`gfn, $sformatf("Advance key manager state from %0s", current_state.name), UVM_MEDIUM)
    ral.control.start.set(1'b1);
    ral.control.operation.set(keymgr_pkg::OpAdvance);
    csr_update(.csr(ral.control));
    ral.control.start.set(1'b0);

    if (wait_done) begin
      wait_op_done(.is_gen_output(0));
      `DV_CHECK_EQ(current_state, exp_next_state)
    end
  endtask : keymgr_advance

  // by default generate for software
  virtual task keymgr_generate(bit identity = 0, bit wait_done = 1);
    bit [2:0] operation;

    `uvm_info(`gfn, "Generate key manager output", UVM_MEDIUM)
    ral.control.start.set(1'b1);

    if (identity) begin
      operation = keymgr_pkg::OpGenId;
    end else begin
      operation = keymgr_pkg::OpGenSwOut;
    end
    ral.control.operation.set(operation);
    csr_update(.csr(ral.control));
    ral.control.start.set(1'b0);

    if (wait_done) wait_op_done(.is_gen_output(1));
  endtask : keymgr_generate

  virtual task keymgr_rd_clr();
    bit [31:0] value[8];
    `uvm_info(`gfn, "Read generated output", UVM_MEDIUM)

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
      `uvm_info(`gfn, $sformatf("Generated output %0d: 0x%0h", i, value[i]), UVM_MEDIUM)
    end

    csr_rd_check(.ptr(ral.sw_share0_output_0), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_1), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_2), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_3), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_4), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_5), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_6), .compare_value('0));
    csr_rd_check(.ptr(ral.sw_share0_output_7), .compare_value('0));

  endtask : keymgr_rd_clr

  // issue any operation in a non-working state to trigger op error
  virtual task keymgr_random_op(bit start, bit init=0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.control,
                                   start.value == local::start;)

    if (init) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      ral.control.operation.set(op_before_init);
    end

    `uvm_info(`gfn, $sformatf("Issuing OP: %0d at state %0s",
                              ral.control.operation.get(), current_state), UVM_MEDIUM)
    csr_update(.csr(ral.control));
    wait_op_done(.is_gen_output(0));

    ral.control.set(0); // clear random value
  endtask

endclass : keymgr_base_vseq
