// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all i2c seqs (except below seqs) in one seq to run sequentially
// 1. override_vseq requires scb to be disabled
class i2c_stress_all_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_stress_all_vseq)

  `uvm_object_new

  rand bit random_reset;

  constraint random_reset_c { random_reset dist {0 :/ 1, 1 :/ 3}; }

  task body();
    string seq_names[] = {"i2c_common_vseq",
                          "i2c_sanity_vseq",
                          "i2c_fifo_full_vseq",
                          "i2c_fifo_overflow_vseq",
                          "i2c_fifo_watermark_vseq",
                          "i2c_fifo_full_vseq",
                          "i2c_stretch_timeout_vseq",
                          "i2c_override_vseq",
                          "i2c_error_intr_vseq",
                          "i2c_perf_vseq"};

    string msg, seq_name;
    int    seq_run_hist[string];

    `uvm_info(`gfn, $sformatf("\n>>> stress_all, total stressed sequences %0d",
        seq_names.size()), UVM_LOW)
    `uvm_info(`gfn, $sformatf("\n>>> stress_all, en_dv_check_vseq %0d, do_dut_init %0d",
        cfg.en_dv_check_vseq, do_dut_init), UVM_LOW)
    for (int i = 1; i <= seq_names.size(); i++) begin
      seq_run_hist[seq_names[i-1]] = 0;
    end

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_runs)
    for (int i = 1; i <= num_runs; i++) begin
      uvm_sequence   seq;
      i2c_base_vseq  i2c_vseq;
      uint           seq_idx = $urandom_range(0, seq_names.size() - 1);

      seq_name = seq_names[seq_idx];
      `uvm_info(`gfn, $sformatf("\n>>> stress_all, run vseq %0d/%0d, start %s ",
          i, num_runs, seq_name), UVM_LOW)
      seq = create_seq_by_name(seq_name);
      `downcast(i2c_vseq, seq)

      // if upper seq disables do_dut_init for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_dut_init) begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(random_reset)
        i2c_vseq.do_dut_init = random_reset;
        `uvm_info(`gfn, "\n  randomly issue reset", UVM_LOW)
      end else begin
        `uvm_info(`gfn, "\n  upper_seq may drive reset thus not issue reset", UVM_DEBUG)
        i2c_vseq.do_dut_init = 0;
      end

      i2c_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(i2c_vseq)
      if (seq_name == "i2c_common_vseq") begin
        i2c_common_vseq common_vseq;
        `downcast(common_vseq, i2c_vseq);
        common_vseq.common_seq_type = "intr_test";
      end
      seq_run_hist[seq_name]++;
      i2c_vseq.start(p_sequencer);
      `uvm_info(`gfn, $sformatf("\n  stress_all, finish vseq %s", seq_name), UVM_LOW)
    end
    // print running histogram for vseq
    msg = {msg, "\n\n>>> stress_all, sequence run histogram:"};
    for (int i = 0; i < seq_names.size(); i++) begin
      seq_name = seq_names[i];
      msg = {msg, $sformatf("\n  %-25s  %2d/%2d", seq_name, seq_run_hist[seq_name], num_runs)};
    end
    `uvm_info(`gfn, $sformatf("%s\n", msg), UVM_LOW)
  endtask : body

endclass : i2c_stress_all_vseq
