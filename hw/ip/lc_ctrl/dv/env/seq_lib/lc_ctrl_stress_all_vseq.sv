// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all lc_ctrl seqs (except below seqs) in one seq to run sequentially
// 1. csr seq, which requires scb to be disabled
// 2. lc_ctrl_rx_oversample_vseq, which requires zero_delays as it's very timing sensitive
class lc_ctrl_stress_all_vseq extends lc_ctrl_base_vseq;
  `uvm_object_utils(lc_ctrl_stress_all_vseq)

  `uvm_object_new

  // Use JTAG for this test.
  rand bit use_jtag;
  uvm_reg_map jtag_map;
  uvm_reg_map tl_map;


  constraint num_trans_c {num_trans inside {[3 : 10]};}

  virtual task pre_start();
    super.pre_start();
    // Find the jtag and tilelink adress map.
    jtag_map = ral.get_map_by_name("jtag_riscv_map");
    `DV_CHECK_NE_FATAL(jtag_map, null)
    tl_map = ral.get_map_by_name("default_map");
    `DV_CHECK_NE_FATAL(tl_map, null)
  endtask

  task body();
    string seq_names[] = {"lc_ctrl_smoke_vseq",
                          "lc_ctrl_lc_errors_vseq",
                          "lc_ctrl_prog_failure_vseq",
                          "lc_ctrl_regwen_during_op_vseq",
                          "lc_ctrl_state_post_trans_vseq",
                          "lc_ctrl_state_failure_vseq"};

    // Short delay after initial reset
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 5));

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence      seq;
      lc_ctrl_base_vseq lc_ctrl_vseq;
      uint              seq_idx = $urandom_range(0, seq_names.size - 1);

      `DV_CHECK_RANDOMIZE_FATAL(this)

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(lc_ctrl_vseq, seq)

      // Randomly choose TL or JTAG for register access
      if (use_jtag && (cfg.jtag_riscv_map != null)) begin
        cfg.jtag_csr = 1;
        cfg.alert_max_delay = 15000;
        cfg.ral.set_default_map(jtag_map);
      end else begin
        cfg.jtag_csr = 0;
        cfg.alert_max_delay = 2000;
        cfg.ral.set_default_map(tl_map);
      end


      lc_ctrl_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(lc_ctrl_vseq)
      if (seq_names[seq_idx] == "lc_ctrl_common_vseq") begin
        lc_ctrl_common_vseq common_vseq;
        `downcast(common_vseq, lc_ctrl_vseq);
        common_vseq.common_seq_type = "intr_test";
      end
      `uvm_info(`gfn, $sformatf("body: executing sequence %s", lc_ctrl_vseq.get_type_name()),
                UVM_MEDIUM)
      lc_ctrl_vseq.start(p_sequencer);

    end
  endtask : body

endclass
