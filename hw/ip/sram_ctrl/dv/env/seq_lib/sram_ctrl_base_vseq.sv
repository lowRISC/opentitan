// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (sram_ctrl_reg_block),
    .CFG_T               (sram_ctrl_env_cfg),
    .COV_T               (sram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (sram_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(sram_ctrl_base_vseq)
  `uvm_object_new

  // various knobs to enable certain routines
  bit do_sram_ctrl_init = 1'b1;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_sram_ctrl_init) sram_ctrl_init();
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset();
    cfg.lc_vif.init();
    if (kind == "HARD") begin
      cfg.otp_clk_rst_vif.apply_reset();
    end
  endtask

  virtual task dut_shutdown();
    // check for pending sram_ctrl operations and wait for them to complete
  endtask

  // setup basic sram_ctrl features
  virtual task sram_ctrl_init();
    cfg.mem_bkdr_vif.clear_mem();
  endtask

  // Request a new scrambling key from the OTP interface.
  //
  // Will trigger a request to the KDI push_pull agent.
  virtual task req_scr_key();
    csr_wr(.csr(ral.ctrl), .value(1'b1));
  endtask

  // Task to perform a single SRAM read at the specified location
  virtual task do_single_read(bit [TL_AW-1:0] addr,
                              bit             blocking = $urandom_range(0, 1));
    logic [TL_DW-1:0] rdata;
    tl_access(.addr(addr),
              .data(rdata),
              .mask(get_rand_contiguous_mask()),
              .write(1'b0),
              .blocking(blocking),
              .tl_sequencer_h(p_sequencer.sram_tl_sequencer_h));
  endtask

  // Task to perform a single SRAM write at the specified location
  virtual task do_single_write(bit [TL_AW-1:0] addr,
                               bit [TL_DW-1:0] data,
                               bit             blocking = $urandom_range(0, 1));
    tl_access(.addr(addr),
              .data(data),
              .mask(get_rand_contiguous_mask()),
              .write(1'b1),
              .blocking(blocking),
              .tl_sequencer_h(p_sequencer.sram_tl_sequencer_h));
  endtask

  // Task to perform `num_ops` fully randomized memory transactions.
  virtual task do_rand_ops(int num_ops,
                           bit blocking = $urandom_range(0, 1));
    bit [TL_DW-1:0] data;
    bit [TL_AW-1:0] addr;
    bit we;
    repeat (num_ops) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `DV_CHECK_STD_RANDOMIZE_FATAL(we)
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr)

      tl_access(.addr(addr),
                .data(data),
                .mask(get_rand_contiguous_mask()),
                .write(we),
                .blocking(blocking),
                .tl_sequencer_h(p_sequencer.sram_tl_sequencer_h));
    end
  endtask

endclass : sram_ctrl_base_vseq
