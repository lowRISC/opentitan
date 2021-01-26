// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all gpio seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
// 2. gpio_cfg_update_on_fly, which requires zero_delays as it's very timing sensitive
class gpio_stress_all_vseq extends gpio_base_vseq;
  `uvm_object_utils(gpio_stress_all_vseq)

  `uvm_object_new

  task body();
    string seq_names[] = {"gpio_smoke_vseq",
                          // "gpio_common_vseq",
                          // does not support intr_test as plus_arg disable do_clear_all_interrupts
                          "gpio_random_dout_din_vseq",
                          "gpio_dout_din_regs_random_rw_vseq",
                          "gpio_intr_rand_pgm_vseq",
                          "gpio_rand_intr_trigger_vseq",
                          "gpio_random_long_reg_writes_reg_reads_vseq"};
    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence   seq;
      gpio_base_vseq gpio_vseq;
      uint           seq_idx = $urandom_range(0, seq_names.size - 1);

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(gpio_vseq, seq)

      // hard_reset in dut_init can be skipped
      if (do_apply_reset) gpio_vseq.do_init_reset = $urandom_range(0, 1);
      else gpio_vseq.do_init_reset = 0;

      gpio_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(gpio_vseq)
      `uvm_info(`gfn, $sformatf("seq_idx = %0d, sequence is %0s", seq_idx, gpio_vseq.get_name()),
                UVM_HIGH)

      gpio_vseq.start(p_sequencer);
      `uvm_info(`gfn, $sformatf("End of sequence %0s with seq_idx = %0d", gpio_vseq.get_name(),
          seq_idx), UVM_HIGH)
    end
  endtask : body
endclass
