// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence extends the automated mem tests to the SRAM memory interface.
//
// However, as the SRAM supports all kinds of reads/writes at any granularity,
// the only error case that can be used here is the `tl_protocol_err` error sequence.
//
// This error sequence is interleaved with a series of random accesses to stress
// memory operation.
class sram_ctrl_mem_tl_errors_vseq extends sram_ctrl_multiple_keys_vseq;

  `uvm_object_utils(sram_ctrl_mem_tl_errors_vseq)
  `uvm_object_new

  virtual task body();
    run_tl_errors_vseq(num_trans);
  endtask : body

  virtual task run_tl_errors_vseq(int num_times = 1, bit do_wait_clk = 0);
    for (int i = 0; i < num_times; i++) begin
      `uvm_info(`gfn, $sformatf("Running run_tl_errors_vseq %0d/%0d", i, num_times), UVM_LOW)

      // spawn various threads to interleave TLUL protocol error accesses and valid memory accesses
      fork
        begin: isolation
          repeat ($urandom_range(5, 20)) begin
            fork
              begin
                randcase
                  2: tl_protocol_err(p_sequencer.sram_tl_sequencer_h);
                  1: do_rand_ops(.num_ops($urandom_range(200, 500)));
                endcase
              end
            join_none
          end
          wait fork;
        end: isolation
      join
    end
  endtask

endclass
