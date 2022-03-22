// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all adc_ctrl seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
// 2. adc_ctrl_rx_oversample_vseq, which requires zero_delays as it's very timing sensitive
class adc_ctrl_stress_all_vseq extends adc_ctrl_base_vseq;
  `uvm_object_utils(adc_ctrl_stress_all_vseq)

  `uvm_object_new

  constraint num_trans_c {num_trans inside {[2 : 5]};}

  virtual task pre_start();
    // Disable read of intr_state at the end of the sequence
    do_clear_all_interrupts = 0;
    super.pre_start();
  endtask

  task body();
    string seq_names[] = {"adc_ctrl_smoke_vseq",
                          "adc_ctrl_filters_polled_vseq",
                          "adc_ctrl_filters_interrupt_vseq",
                          "adc_ctrl_filters_both_vseq",
                          "adc_ctrl_clock_gating_vseq",
                          "adc_ctrl_poweron_counter_vseq",
                          "adc_ctrl_lowpower_counter_vseq",
                          "adc_ctrl_fsm_reset_vseq",
                          "adc_ctrl_common_vseq"};

    // Short delay after initial reset
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 5));

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence seq;
      adc_ctrl_base_vseq adc_ctrl_vseq;
      uint seq_idx = $urandom_range(0, seq_names.size - 1);
      // Test sequences which take a long time - restrict to one iteration
      bit long_test = seq_names[seq_idx] inside {"adc_ctrl_filters_polled_vseq",
        "adc_ctrl_filters_interrupt_vseq", "adc_ctrl_filters_both_vseq",
        "adc_ctrl_clock_gating_vseq"};

      `DV_CHECK_RANDOMIZE_FATAL(this)

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(adc_ctrl_vseq, seq)

      adc_ctrl_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(adc_ctrl_vseq, if (long_test) num_trans == 1;)
      if (seq_names[seq_idx] == "adc_ctrl_common_vseq") begin
        adc_ctrl_common_vseq common_vseq;
        `downcast(common_vseq, adc_ctrl_vseq);
        common_vseq.common_seq_type = "intr_test";
      end
      `uvm_info(`gfn, $sformatf("body: executing sequence %s", adc_ctrl_vseq.get_type_name()),
                UVM_LOW)
      adc_ctrl_vseq.start(p_sequencer);

    end
  endtask : body
endclass
