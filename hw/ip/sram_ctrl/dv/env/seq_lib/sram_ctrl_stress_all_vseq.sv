// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// combine all sram_ctrl vseqs (except the ones belwo) in one top level vseq to run sequentially
// 1. common vseq: csr/alert tests disable scb, and sram does not have interrupts
// 2. lc_escalation_vseq can issue an internal reset, so it is included in stress_all_vseq,
//    but excluded from stress_all_with_rand_reset
class sram_ctrl_stress_all_vseq extends sram_ctrl_base_vseq;

  `uvm_object_utils(sram_ctrl_stress_all_vseq)
  `uvm_object_new

  string vseq_names[$] = {"sram_ctrl_smoke_vseq",
                         "sram_ctrl_multiple_keys_vseq",
                         "sram_ctrl_bijection_vseq",
                         "sram_ctrl_executable_vseq",
                         "sram_ctrl_regwen_vseq"};

  constraint num_trans_c {
    num_trans inside {[4:8]};
  }

  virtual task pre_start();
    super.pre_start();
    if (common_seq_type != "stress_all_with_rand_reset") begin
      vseq_names.push_back("sram_ctrl_lc_escalation_vseq");
    end
  endtask

  task body();
    `uvm_info(`gfn, $sformatf("Running %0d random sequences", num_trans), UVM_LOW)
    for (int i = 0; i < num_trans; i++) begin
      uvm_sequence        seq;
      sram_ctrl_base_vseq sram_vseq;
      uint                seq_idx = $urandom_range(0, vseq_names.size() - 1);
      string              cur_vseq_name = vseq_names[seq_idx];

      seq = create_seq_by_name(cur_vseq_name);
      `downcast(sram_vseq, seq)

      // Wait a few cycles until the memory init request is finished. Without
      // this wait, we could land up resetting the SRAM controller when the last
      // write of the memory init is in the write pipeline. This could result in
      // having an uninitialized memory.
      if (i == 0) begin
        cfg.clk_rst_vif.wait_clks(2);
      end
      sram_vseq.do_apply_reset = (do_apply_reset) ? $urandom_range(0, 1) : 0;

      sram_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(sram_vseq)
      sram_vseq.do_sram_ctrl_init = 0;
      `uvm_info(`gfn, $sformatf("iteration[%0d]: starting %0s", i, cur_vseq_name), UVM_LOW)
      sram_vseq.start(p_sequencer);
      `uvm_info(`gfn, $sformatf("iteration[%0d]: finishing %0s", i, cur_vseq_name), UVM_MEDIUM)
    end
  endtask

endclass
