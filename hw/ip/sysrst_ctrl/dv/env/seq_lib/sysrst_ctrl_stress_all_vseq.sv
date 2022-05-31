// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all sysrst_ctrl seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
class sysrst_ctrl_stress_all_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_stress_all_vseq)

  `uvm_object_new

  constraint num_trans_c {num_trans inside {[2 : 5]};}

  task body();
  uvm_reg_data_t rdata;
    string seq_names[] = {"sysrst_ctrl_smoke_vseq",
                          "sysrst_ctrl_in_out_inverted_vseq",
                          "sysrst_ctrl_combo_detect_ec_rst_vseq",
                          "sysrst_ctrl_auto_blk_key_output_vseq",
                          "sysrst_ctrl_pin_access_vseq",
                          "sysrst_ctrl_pin_override_vseq",
                          "sysrst_ctrl_flash_wr_prot_vseq",
                          "sysrst_ctrl_ec_pwr_on_rst_vseq",
                          "sysrst_ctrl_flash_wr_prot_vseq",
                          "sysrst_ctrl_ultra_low_pwr_vseq",
                          "sysrst_ctrl_combo_detect_vseq",
                          "sysrst_ctrl_edge_detect_vseq",
                          "sysrst_ctrl_common_vseq"};

    // Short delay after initial reset
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 5));

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence          seq;
      sysrst_ctrl_base_vseq sysrst_ctrl_vseq;
      uint                  seq_idx = $urandom_range(0, seq_names.size - 1);
      // Test sequences which take a long time - restrict to one iteration
      bit long_test = seq_names[seq_idx] inside {"sysrst_ctrl_ultra_low_pwr_vseq"};

      `DV_CHECK_RANDOMIZE_FATAL(this)

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(sysrst_ctrl_vseq, seq)

      sysrst_ctrl_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(sysrst_ctrl_vseq, if (long_test) num_trans == 1;)
      if (seq_names[seq_idx] == "sysrst_ctrl_common_vseq") begin
        sysrst_ctrl_common_vseq common_vseq;
        `downcast(common_vseq, sysrst_ctrl_vseq);
        common_vseq.common_seq_type = "intr_test";
      end
      `uvm_info(`gfn, $sformatf("body: executing sequence %s", sysrst_ctrl_vseq.get_type_name()),
                UVM_LOW)

      sysrst_ctrl_vseq.start(p_sequencer);

    end
  endtask : body

endclass
