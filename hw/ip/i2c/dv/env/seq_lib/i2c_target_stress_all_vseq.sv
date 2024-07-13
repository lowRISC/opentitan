// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test runs a number of different virtual sequences back-to-back to cover a wider
// gamut of stimulus.
//
class i2c_target_stress_all_vseq extends i2c_base_vseq;

  ///////////////
  // VARIABLES //
  ///////////////

  local int seq_run_hist[string];

  // The following sequence names are all candidates to be run as part of the stress test.
  string seq_names[$] = {
    "i2c_target_smoke_vseq",
    "i2c_target_stress_wr_vseq",
    "i2c_target_timeout_vseq",
    "i2c_target_ack_stop_vseq",
    "i2c_target_perf_vseq"
  };

  `uvm_object_utils(i2c_target_stress_all_vseq)
  `uvm_object_new

  /////////////
  // METHODS //
  /////////////


  virtual task pre_start();
    super.pre_start();

    // Initialize the sequence history map
    for (int i = 1; i <= seq_names.size(); i++) seq_run_hist[seq_names[i-1]] = 0;

    // Disable reset-application between sequences
    // This may be re-enabled in the future if there is any test coverage to be achieved by it,
    // so it can remain for now. However, the stress_all_with_rand_reset tests are likely to be
    // better for closing coverage around resets.
    do_apply_reset = 1'b0;
    `uvm_info(`gfn, $sformatf("stress_all_vseq.do_apply_reset=1'b%1b", do_apply_reset), UVM_MEDIUM)

    // Print out any sequences we may run as part of the stress test.
    print_seq_names(seq_names);
  endtask : pre_start


  virtual task body();
    // Initialize the DUT/Agent as Target/Controller respectively.
    // This provides an initial configuration of the DUT's CSRs, as well as configuring both DUT
    // and Agent with a compatible set of timing parameters.
    initialization();

    `uvm_info(`gfn, "i2c_target_stress_all_vseq : Initialization completed.", UVM_HIGH)

    // Drive the stimulus sequences.
    for (int i = 1; i <= num_runs; i++) begin
      string seq_name; // The name of the current stimulus sequence
      uint seq_idx = $urandom_range(0, seq_names.size() - 1);

      `uvm_info(`gfn, $sformatf("-> (%0d/%0d) Start of stimulus vseq '%0s'",
        i, num_runs, seq_names[seq_idx]), UVM_LOW)

      seq_name = seq_names[seq_idx];

      begin
        i2c_base_vseq i2c_vseq;
        begin
          uvm_sequence seq;
          seq = create_seq_by_name(seq_name);
          `downcast(i2c_vseq, seq)
        end
        i2c_vseq.do_apply_reset = (do_apply_reset) ? $urandom_range(0, 1) :
                                                     0;

        `uvm_info(`gfn, $sformatf("For the following vseq, %0s.do_apply_reset=1'b%1b",
          seq_name, i2c_vseq.do_apply_reset), UVM_MEDIUM)

        i2c_vseq.set_sequencer(p_sequencer);
        `DV_CHECK_RANDOMIZE_FATAL(i2c_vseq)
        i2c_vseq.start(p_sequencer);
      end

      `uvm_info(`gfn, $sformatf("-> (%0d/%0d) End of stimulus vseq '%0s'",
        i, num_runs, seq_name), UVM_LOW)
      seq_run_hist[seq_name]++;

      // Reset the flag for the next sequence
      cfg.stop_intr_handler = 0;
    end

    // We've now finished running all the stimulus sequences
    // Wait for the DUT's target-module to return to idle, given there is no more stimulus.
    wait_for_target_idle();

    // Print a histogram/summary of the vseq's we ran
    print_seq_histogram_summary();

    `uvm_info(`gfn, "End of i2c_target_stress_all_vseq.", UVM_MEDIUM)
  endtask : body


  virtual function void print_seq_names(string seq_names[]);
    string str;
    str = $sformatf("\nThe following list of %0d vseqs will be stressed:", seq_names.size());
    for (int i = 0; i < seq_names.size(); i++) begin
      str = {str, $sformatf("\n - %s", seq_names[i])};
    end
    `uvm_info(`gfn, $sformatf("%s", str), UVM_MEDIUM)
  endfunction : print_seq_names


  virtual function void print_seq_histogram_summary();
    string str = "\ni2c_target_stress_all_vseq -> run histogram:";
    for (int i = 0; i < seq_names.size(); i++) begin
      string seq_name = seq_names[i];
      str = {str, $sformatf("\n  %-25s  %2d / %2d", seq_name, seq_run_hist[seq_name], num_runs)};
    end
    `uvm_info(`gfn, $sformatf("%s", str), UVM_MEDIUM)
  endfunction : print_seq_histogram_summary


endclass : i2c_target_stress_all_vseq
