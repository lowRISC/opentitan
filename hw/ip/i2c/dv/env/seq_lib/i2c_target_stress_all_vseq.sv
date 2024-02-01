// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all i2c seqs (except below vseqs) in one seq to run sequentially
// 1. override_vseq requires scb and monitor to be disabled
// 2. csr seq, which requires scb to be disabled
// 3. i2c_error_intr_vseq can issue internal reset
//    so it is excluded/included w.r.t stress_all_with_rand_reset/stress_all test

class i2c_target_stress_all_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stress_all_vseq)

  `uvm_object_new

  local string str, seq_name;
  local int    seq_run_hist[string];

  string seq_names[$] = {
    "i2c_target_smoke_vseq",
    "i2c_target_stress_wr_vseq",
    "i2c_target_timeout_vseq",
    "i2c_target_ack_stop_vseq",
    "i2c_target_perf_vseq"
  };

  virtual task body();
    `uvm_info(`gfn, "\n\n=> start i2c_target_stress_all_vseq", UVM_DEBUG)
    print_seq_names(seq_names);
    initialization();
    for (int i = 1; i <= seq_names.size(); i++) begin
      seq_run_hist[seq_names[i-1]] = 0;
    end

    for (int i = 1; i <= num_runs; i++) begin
      uvm_sequence   seq;
      i2c_base_vseq  i2c_vseq;
      uint           seq_idx = $urandom_range(0, seq_names.size() - 1);
      cfg.stop_intr_handler = 0;

      seq_name = seq_names[seq_idx];
      `uvm_info(`gfn, $sformatf("\n  -> start stressing vseq %s (%0d/%0d)",
                                seq_name, i, num_runs), UVM_LOW)
      seq = create_seq_by_name(seq_name);
      `downcast(i2c_vseq, seq)
      // do_apply_reset is defined in dv_base_vseq
      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      `uvm_info(`gfn, $sformatf("\n  do_apply_reset %b", do_apply_reset), UVM_MEDIUM)
      if (do_apply_reset) begin
        i2c_vseq.do_apply_reset = $urandom_range(0, 1);
        if (i2c_vseq.do_apply_reset) begin
          `uvm_info(`gfn, "\n  stressing reset is randomly issued with stress_test", UVM_MEDIUM)
        end
      end else begin
        i2c_vseq.do_apply_reset = 0;
        `uvm_info(`gfn, "\n  reset may be driven by upper_seq thus not be issued", UVM_DEBUG)
      end
      // Need to reset scoreboard whenever sequence start over regardless of dut reset
      cfg.scb_h.reset("SOFT");

      i2c_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(i2c_vseq)
      // run vseq
      i2c_vseq.start(p_sequencer);
      seq_run_hist[seq_name]++;

      `uvm_info(`gfn, $sformatf("\n  -> end stressing vseq %s\n", seq_name), UVM_LOW)
      wait(cfg.m_i2c_agent_cfg.vif.rst_ni);
    end
    wait_for_target_idle();
    `uvm_info(`gfn, "\n=> end of i2c_target_stress_all_vseq", UVM_MEDIUM)

    // get the histogram of vseq running
    str = {str, "\n\n=> vseq run histogram:"};
    for (int i = 0; i < seq_names.size(); i++) begin
      seq_name = seq_names[i];
      str = {str, $sformatf("\n  %-25s  %2d / %2d", seq_name, seq_run_hist[seq_name], num_runs)};
    end
    `uvm_info(`gfn, $sformatf("%s\n", str), UVM_DEBUG)
  endtask : body

  virtual function void print_seq_names(string seq_names[]);
    string str;

    `uvm_info(`gfn, $sformatf("\n  list of %0d vseqs are stressed", seq_names.size()), UVM_DEBUG)
    for (int i = 1; i <= seq_names.size(); i++) begin
      str = {str, $sformatf("\n    %s", seq_names[i-1])};
    end
    `uvm_info(`gfn, $sformatf("%s", str), UVM_DEBUG)
  endfunction : print_seq_names

endclass : i2c_target_stress_all_vseq
