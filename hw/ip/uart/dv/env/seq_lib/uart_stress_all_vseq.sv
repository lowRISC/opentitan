// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all uart seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
// 2. uart_rx_oversample_vseq, which requires zero_delays as it's very timing sensitive
class uart_stress_all_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_stress_all_vseq)

  `uvm_object_new

  task body();
    string seq_names[] = {"uart_sanity_vseq",
                          "uart_tx_rx_vseq",
                          "uart_fifo_full_vseq",
                          "uart_fifo_overflow_vseq",
                          "uart_fifo_reset_vseq",
                          "uart_intr_testmode_vseq",
                          "uart_intr_vseq",
                          "uart_noise_filter_vseq",
                          "uart_rx_start_bit_filter_vseq",
                          "uart_perf_vseq",
                          "uart_loopback_vseq"};
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence   seq;
      uart_base_vseq uart_seq;
      uint           seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(uart_seq, seq)

      // dut_init (reset) can be skipped after the 1st seq
      if (i > 0) uart_seq.do_dut_init = $urandom_range(0, 1);

      uart_seq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(uart_seq)
      uart_seq.start(p_sequencer);
    end
  endtask : body

endclass
