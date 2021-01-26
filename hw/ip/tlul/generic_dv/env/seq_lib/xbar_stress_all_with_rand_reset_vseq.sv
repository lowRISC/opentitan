// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// one thread running the hmac_stress_all sequence
// another thread randomly insert reset
class xbar_stress_all_with_rand_reset_vseq extends xbar_base_vseq;
  `uvm_object_utils(xbar_stress_all_with_rand_reset_vseq)

  rand uint delay;

  `uvm_object_new

  constraint delay_c {
    delay dist {
      0                   :/ 1,
      [1      :100]       :/ 1,
      [101    :10_000]    :/ 8,
      [10_001 :1_000_000] :/ 1
    };
  }

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit reset_ongoing;
      xbar_stress_all_vseq xbar_vseq;
      fork
        begin : seq_wo_reset
          xbar_vseq = xbar_stress_all_vseq::type_id::create("xbar_stress_all_vseq");

          xbar_vseq.do_apply_reset = 0;
          xbar_vseq.set_sequencer(p_sequencer);
          `DV_CHECK_RANDOMIZE_FATAL(xbar_vseq)
          xbar_vseq.start(p_sequencer);
          // once reset starts, need to wait until reset is done
          wait (reset_ongoing == 0);
          `uvm_info(`gfn, $sformatf("Finished run %0d/%0d w/o reset", i, num_trans), UVM_LOW)
        end

        begin : reset
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay,
                                             delay dist {
                                                 1                   :/ 1,
                                                 [2      :100]       :/ 1,
                                                 [101    :10_000]    :/ 8,
                                                 [10_001 :1_000_000] :/ 1
                                             };)
          cfg.clk_rst_vif.wait_clks(delay);
          reset_ongoing = 1;
          // reset needs to be longger than any clocks to allow TLUL driver flash out all items
          cfg.clk_rst_vif.apply_reset(.reset_width_clks($urandom_range(100, 200)));
          reset_ongoing = 0;
          `uvm_info(`gfn, $sformatf("Reset is issued for run %0d/%0d", i, num_trans), UVM_LOW)
        end
      join_any
      foreach (p_sequencer.host_seqr[i])   p_sequencer.host_seqr[i].stop_sequences();
      foreach (p_sequencer.device_seqr[i]) p_sequencer.device_seqr[i].stop_sequences();
      disable fork;
      // delay to avoid race condition when sending item and checking no item after reset occur at
      // the same time
      #1ps;
    end // end for loop
  endtask : body

endclass
