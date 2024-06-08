// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to insert 1 or 2 bit flips to base register file read outputs.
// Time it so that only when a registers gets used, data corruption happen.

class otbn_rf_base_intg_err_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_rf_base_intg_err_vseq)

  `uvm_object_new
  rand bit insert_intg_err_to_a;

  // Wait until the selected register file is being used
  //
  // This will normally just be a couple of cycles (because most instructions read from the register
  // file), but it might be a bit longer if we happen to be stalled waiting for the EDN, which
  // happens on a RND read.
  task await_use(ref bit seen_use);
    logic rd_en;
    `uvm_info(`gfn, "Waiting for selected RF to be used", UVM_LOW)
    fork begin : isolation_fork
      fork
        // Wait until we can see a read on the expected side
        do begin
          @(cfg.clk_rst_vif.cbn);
          rd_en = insert_intg_err_to_a ?
                  cfg.trace_vif.rf_base_rd_en_a : cfg.trace_vif.rf_base_rd_en_b;
        end while(!rd_en);
        // Wait until the program stops running. If it has stopped, there definitely won't be a read
        // in the future.
        wait (cfg.model_agent_cfg.vif.status != otbn_pkg::StatusBusyExecute);
      join_any
      disable fork;
    end join
    seen_use = rd_en;
  endtask

  // Start running a program through OTBN and finish the task on a cycle when the selected register
  // file is being used.
  task run_until_use();
    int num_tries = 4;

    repeat (num_tries) begin
      bit seen_use;

      // Start running OTBN. When this task returns, we'll be in the middle of a run.
      start_running_otbn(.check_end_addr(1'b0));

      // Now wait until the register file is being used
      await_use(seen_use);

      // We expect that to have worked (so seen_use is true). In that case, we can return.
      if (seen_use) return;

      // The program run has completed. Before we try again, we need to allow OTBN to finish its
      // current operation (to allow it to do the secure wipe after the run). Wait until we get to
      // Idle. In theory, we might get to Locked, but that shouldn't happen when running a standard
      // binary without outside interference!
      wait (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle);
    end

    // The test run completed several times while we were waiting to see a read on the expected
    // side. This shouldn't really happen, because it means that start_running_otbn() picked a time
    // that was "almost at the end" of the program several times in a row.
    `uvm_fatal(`gfn,
               $sformatf("Program completed %d times before using register file %0s.",
                         num_tries, insert_intg_err_to_a ? "A" : "B"))
  endtask

  function bit [otbn_pkg::BaseIntgWidth-1:0] corrupt_data(
      input bit [otbn_pkg::BaseIntgWidth-1:0] orig_data
    );
    bit [otbn_pkg::BaseIntgWidth-1:0] mask;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
    return cfg.fix_integrity_32(orig_data) ^ mask;
  endfunction

  task inject_errors();
    logic [otbn_pkg::BaseIntgWidth-1:0] orig_data;
    bit [otbn_pkg::BaseIntgWidth-1:0] new_data;
    orig_data = insert_intg_err_to_a ? cfg.trace_vif.rf_base_rd_data_a :
                                       cfg.trace_vif.rf_base_rd_data_b;
    new_data = corrupt_data(orig_data);
    `uvm_info(`gfn, "Injecting errors into Base RF", UVM_LOW)
    if (insert_intg_err_to_a) begin
      cfg.rf_base_vif.force_rf_base_rd_data_a_intg(new_data);
    end else begin
      cfg.rf_base_vif.force_rf_base_rd_data_b_intg(new_data);
    end
  endtask

  task release_force();
    if (insert_intg_err_to_a) begin
      cfg.rf_base_vif.release_rf_base_rd_data_a_intg();
    end else begin
      cfg.rf_base_vif.release_rf_base_rd_data_b_intg();
    end
  endtask

  task body();
    uvm_reg_data_t             act_val;
    string                     elf_path;
    bit [BaseWordsPerWLEN-1:0] corrupted_words;
    bit [ExtWLEN-1:0]          new_data;
    otbn_pkg::err_bits_t err_bits;

    elf_path = pick_elf_path();
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, 1'b1);

    // Start running OTBN. When this task returns, we'll be in the middle of a run and executing an
    // instruction that reads from the selected register file.
    run_until_use();

    inject_errors();

    // Notify the model about the integrity violation error.
    err_bits = '{reg_intg_violation: 1'b1, default: 1'b0};
    cfg.model_agent_cfg.vif.send_err_escalation(err_bits);

    @(cfg.clk_rst_vif.cbn);
    release_force();

    // OTBN should now do a secure wipe
    wait_secure_wipe();

    // We should now be in a locked state after the secure wipe.
    `DV_CHECK_FATAL(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked);
    // The scoreboard will have seen the transition to locked state and inferred that it should
    // see a fatal alert. However, it doesn't really have a way to ensure that we keep generating
    // them.  Wait for 3 fatal alerts and also read STATUS, ERR_BITS and FATAL_ALERT_CAUSE in
    // parallel.
    fork
      begin
        csr_utils_pkg::csr_rd(.ptr(ral.status), .value(act_val));
        csr_utils_pkg::csr_rd(.ptr(ral.err_bits), .value(act_val));
        csr_utils_pkg::csr_rd(.ptr(ral.fatal_alert_cause), .value(act_val));
      end
      begin
        repeat (3) wait_alert_trigger("fatal", .wait_complete(1));
      end
    join

    // Reset and finish sequence.
    do_apply_reset = 1'b1;
    dut_init("HARD");
  endtask

endclass
