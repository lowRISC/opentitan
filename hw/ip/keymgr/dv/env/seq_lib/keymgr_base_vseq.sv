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

  // save DUT returned current state here, rather than using it from RAL, it's needed info to
  // predict operation result in seq
  keymgr_pkg::keymgr_working_state_e current_state;

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
    `uvm_info(`gfn, "Initializating key manager", UVM_MEDIUM)
    ral.control.init.set(1'b1);
    csr_update(.csr(ral.control));
    csr_spinwait(.ptr(ral.working_state), .exp_data(keymgr_pkg::StInit));
    // manually clear here since ral is not aware this bet is self-clearing
    ral.control.init.set(1'b0);
  endtask : keymgr_init

  // advance to next state and generate output, clear output
  virtual task keymgr_operations(keymgr_pkg::keymgr_working_state_e exp_next_state,
                                 bit gen_output = $urandom_range(0, 1),
                                 bit clr_output = $urandom_range(0, 1));
    `uvm_info(`gfn, "Start keymgr_operations", UVM_HIGH)
    keymgr_advance(exp_next_state);
    if (gen_output) begin
      repeat ($urandom_range(1, 4)) begin
        keymgr_generate(.identity($urandom_range(0, 1)));
        if (clr_output) keymgr_rd_clr();
      end
    end
  endtask : keymgr_operations

  virtual task wait_op_done(bit is_gen_output);
    keymgr_pkg::keymgr_op_status_e exp_status;
    bit is_good_op = 1;
    int key_verion = ral.key_version.get_mirrored_value();

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
      is_good_op = current_state inside {keymgr_pkg::StInit,
                                         keymgr_pkg::StCreatorRootKey,
                                         keymgr_pkg::StOwnerIntKey,
                                         keymgr_pkg::StOwnerKey};
    end
    `uvm_info(`gfn, $sformatf("Wait for operation done in state %0s, gen_out %0d",
                              current_state.name, is_gen_output), UVM_MEDIUM)

    // wait for status to get out of OpWip and check
    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_pkg::OpWip),
                 .compare_op(CompareOpNe));
    exp_status = is_good_op ? keymgr_pkg::OpDoneSuccess : keymgr_pkg::OpDoneFail;
    `DV_CHECK_EQ_FATAL(ral.op_status.status.get_mirrored_value(), exp_status)
  endtask : wait_op_done

  virtual task keymgr_advance(keymgr_pkg::keymgr_working_state_e exp_next_state);
    bit [TL_DW-1:0] rdata;

    csr_rd(.ptr(ral.working_state), .value(rdata));
    `downcast(current_state, rdata)
    `uvm_info(`gfn, $sformatf("Advance key manager state from %0s", current_state.name), UVM_MEDIUM)
    ral.control.start.set(1'b1);
    ral.control.operation.set(keymgr_pkg::OpAdvance);
    csr_update(.csr(ral.control));

    wait_op_done(.is_gen_output(0));
    csr_rd_check(.ptr(ral.working_state), .compare_value(exp_next_state));
    current_state = exp_next_state;
  endtask : keymgr_advance


  // by default generate for software
  virtual task keymgr_generate(bit identity = 0);
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

    wait_op_done(.is_gen_output(1));
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

endclass : keymgr_base_vseq
