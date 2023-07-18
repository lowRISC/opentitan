// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts an integrity-checked signal while OTBN
// is still running.

class otbn_intg_err_vseq extends otbn_base_vseq;

  `uvm_object_utils(otbn_intg_err_vseq)

  `uvm_object_new

  // Wait until the integrity-checked signal is used (otherwise an injected error would not have any
  // consequences) or an internal timeout expires.  The `used_words` output indicates which words
  // were used during the call of this task.
  protected virtual task await_use(output bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words);
  endtask

  // Probabilistically corrupt 1 to 2 bits of each word of `orig_data`, with a probability of
  // `corrupt_word_pct` (in percent) per word.  The `corrupted_words` output indicates which words
  // were corrupted.
  protected function bit [otbn_pkg::ExtWLEN-1:0] corrupt_data(
      input bit [otbn_pkg::ExtWLEN-1:0] orig_data,
      input int unsigned corrupt_word_pct[otbn_pkg::BaseWordsPerWLEN],
      output bit [otbn_pkg::BaseWordsPerWLEN-1:0] corrupted_words
    );
    bit [otbn_pkg::ExtWLEN-1:0] new_data;
    for (int i_word = 0; i_word < otbn_pkg::BaseWordsPerWLEN; i_word++) begin
      bit [BaseIntgWidth-1:0] orig_word = orig_data[i_word*39+:39];
      bit corrupt_word = $urandom_range(100) < corrupt_word_pct[i_word];
      if (corrupt_word) begin
        bit [BaseIntgWidth-1:0] good_word = cfg.fix_integrity_32(orig_word);
        bit [BaseIntgWidth-1:0] mask;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
        new_data[i_word*39+:39] = good_word ^ mask;
        corrupted_words[i_word] = 1'b1;
      end else begin
        new_data[i_word*39+:39] = orig_word;
        corrupted_words[i_word] = 1'b0;
      end
    end
    return new_data;
  endfunction

  // Inject errors into the integrity-checked signal by `force`ing it.
  protected virtual task inject_errors(input  bit [otbn_pkg::BaseWordsPerWLEN-1:0] used_words,
                                       output bit [otbn_pkg::BaseWordsPerWLEN-1:0] corrupted_words);
  endtask

  // Release the `force`ing of the integrity-checked signal.
  protected virtual task release_force();
  endtask

  task body();
    uvm_reg_data_t             act_val;
    string                     elf_path;
    bit [BaseWordsPerWLEN-1:0] used_words;
    bit [BaseWordsPerWLEN-1:0] corrupted_words;
    bit [ExtWLEN-1:0]          new_data;

    elf_path = pick_elf_path();
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, 1'b1);

    // Start running OTBN. When this task returns, we'll be in the middle of a run.
    start_running_otbn(.check_end_addr(1'b0));

    // Wait until the register containing the integrity-checked value is being used.
    await_use(used_words);

    // If the binary we are running does not use the integrity-checked register, there is no point
    // in continuing this sequence.
    if (used_words == '0) begin
      `uvm_info(`gfn,
          {"Skipping test: we happened to run a binary that does not use ",
          "the register into which we want to inject an integrity error."},
          UVM_LOW)
      return;
    end

    inject_errors(used_words, corrupted_words);

    // Notify the model about the integrity violation error.
    if (|(corrupted_words & used_words)) begin
      otbn_pkg::err_bits_t err_bits;
      err_bits = '{reg_intg_violation: 1'b1, default: 1'b0};
      cfg.model_agent_cfg.vif.send_err_escalation(err_bits);
    end

    @(cfg.clk_rst_vif.cbn);
    release_force();

    if (|(corrupted_words & used_words)) begin
      // OTBN should now do a secure wipe. Give it up to 4000 cycles to do so (because it needs to
      // go twice over all registers and reseed URND in between, the time of which depends on the
      // delay configured in the EDN model).
      cfg.clk_rst_vif.wait_n_clks(4000);

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
    end

    // Reset and finish sequence.
    do_apply_reset = 1'b1;
    dut_init("HARD");
  endtask

endclass
