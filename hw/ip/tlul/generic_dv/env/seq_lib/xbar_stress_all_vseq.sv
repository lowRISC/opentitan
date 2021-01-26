// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all xbar seqs in one seq to run in parallel for mutiply times
class xbar_stress_all_vseq extends xbar_base_vseq;
  `uvm_object_utils(xbar_stress_all_vseq)

  // reduce num_trans
  constraint num_trans_c {
    num_trans inside {[1:5]};
  }

  `uvm_object_new

  task body();
    string seq_names[] = {"xbar_smoke_vseq",
                          "xbar_random_vseq",
                          "xbar_access_same_device_vseq",
                          "xbar_same_source_vseq",
                          "xbar_unmapped_addr_vseq"};
    run_all_device_seq_nonblocking();
    for (int i = 1; i <= num_trans; i++) fork
      begin // isolation thread
        foreach (seq_names[i]) begin
          automatic int seq_idx = i;
          fork
            if ($urandom_range(0, 1)) begin
              uvm_sequence   seq;
              xbar_base_vseq xbar_vseq;
              uint           dly_to_start_seq;

              seq = create_seq_by_name(seq_names[seq_idx]);
              `downcast(xbar_vseq, seq)

              // dut_init (reset) is done in xbar_stress_all_vseq
              xbar_vseq.do_dut_init = 0;
              // rsp thread is created in xbar_stress_all_vseq at line 22
              xbar_vseq.do_device_rsp = 0;

              xbar_vseq.set_sequencer(p_sequencer);
              `DV_CHECK_RANDOMIZE_FATAL(xbar_vseq)
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(dly_to_start_seq,
                                                 dly_to_start_seq dist {
                                                   0           :/ 1,
                                                   [1:100]     :/ 1,
                                                   [101:1000]  :/ 1
                                                 };)
              cfg.clk_rst_vif.wait_clks(dly_to_start_seq);
              xbar_vseq.start(p_sequencer);
            end
          join_none
        end
        wait fork;
        // if this seq is called as a sub-seq, and run with another seq that contains reset,
        // when reset is issued in both seq at the same time, can't know where is the end of reset
        // hence, if we want to kill unfinished seq after reset, we may not kill it at a right time
        if (do_apply_reset && $urandom_range(0, 1)) dut_init();
        `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
      end // isolation thread
    join
  endtask : body

endclass
