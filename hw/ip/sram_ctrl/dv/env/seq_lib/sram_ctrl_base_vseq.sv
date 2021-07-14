// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (sram_ctrl_regs_reg_block),
    .CFG_T               (sram_ctrl_env_cfg),
    .COV_T               (sram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (sram_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(sram_ctrl_base_vseq)
  `uvm_object_new

  // various knobs to enable certain routines
  bit do_sram_ctrl_init = 1'b1;

  bit stress_pipeline = 1'b0;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_sram_ctrl_init) sram_ctrl_init();
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    cfg.lc_vif.init();
    cfg.exec_vif.init();
    if (kind == "HARD") begin
      cfg.otp_clk_rst_vif.apply_reset();
    end
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.otp_clk_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.otp_clk_rst_vif.clk_period_ps);
    cfg.otp_clk_rst_vif.drive_rst_pin(1);
  endtask

  virtual task dut_shutdown();
    // check for pending sram_ctrl operations and wait for them to complete
  endtask

  // setup basic sram_ctrl features
  virtual task sram_ctrl_init();
    req_mem_init();
  endtask

  // Request a memory init.
  //
  virtual task req_mem_init();
    csr_wr(.ptr(ral.ctrl), .value(3));
    csr_spinwait(.ptr(ral.ctrl.init), .exp_data(0));
  endtask

  // Request a new scrambling key from the OTP interface.
  //
  // Will trigger a request to the KDI push_pull agent.
  virtual task req_scr_key();
    csr_wr(.ptr(ral.ctrl), .value(1'b1));
  endtask

  // Task to perform a single SRAM read at the specified location
  virtual task do_single_read(input bit [TL_AW-1:0]    addr,
                              input bit [TL_DBW-1:0]   mask         = get_rand_contiguous_mask(),
                              input bit                blocking     = $urandom_range(0, 1),
                              input bit                check_rdata  = 0,
                              input bit [TL_DW-1:0]    exp_rdata    = '0,
                              input tlul_pkg::tl_type_e tl_type     = tlul_pkg::DataType,
                              output logic [TL_DW-1:0] rdata);
    tl_access(.addr(addr),
              .data(rdata),
              .mask(mask),
              .write(1'b0),
              .blocking(blocking),
              .check_exp_data(check_rdata),
              .exp_data(exp_rdata),
              .compare_mask(mask),
              .tl_type(tl_type),
              .tl_sequencer_h(p_sequencer.sram_tl_sequencer_h));
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // Task to perform a single SRAM write at the specified location
  virtual task do_single_write(bit [TL_AW-1:0]  addr,
                               bit [TL_DW-1:0]  data,
                               bit [TL_DBW-1:0] mask        = get_rand_contiguous_mask(),
                               bit              blocking    = $urandom_range(0, 1),
                               tlul_pkg::tl_type_e tl_type  = tlul_pkg::DataType);
    tl_access(.addr(addr),
              .data(data),
              .mask(mask),
              .write(1'b1),
              .blocking(blocking),
              .tl_type(tl_type),
              .tl_sequencer_h(p_sequencer.sram_tl_sequencer_h));
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // This task is designed to kick off `num_stress_ops` back to back memory transactions
  // to the same address, to stress the SRAM pipelining implementation
  virtual task do_stress_ops(bit [TL_AW-1:0] addr,
                             int num_stress_ops,
                             bit en_ifetch = 0);
    bit [TL_DW-1:0] data;
    tlul_pkg::tl_type_e tl_type;

    repeat (num_stress_ops) begin
      // fully randomize data
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)

      // never send InstrType transactions unless en_ifetch is enabled
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tl_type, !en_ifetch -> tl_type == tlul_pkg::DataType;)

      tl_access(.addr(addr),
                .data(data),
                .mask(get_rand_contiguous_mask()),
                .write($urandom_range(0, 1)),
                .check_rsp(!en_ifetch),
                .blocking(1'b0),
                .tl_type(tl_type),
                .tl_sequencer_h(p_sequencer.sram_tl_sequencer_h));
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // Task to perform `num_ops` fully randomized memory transactions.
  //
  // Includes capability to abort transactions after several cycles if no response
  // is seen from the SRAM.
  // This is useful for when we are testing memory operations during terminal states
  // (such as during LC escalations or parity errors), which are expected to not respond at all.
  virtual task do_rand_ops(int num_ops,
                           bit blocking  = $urandom_range(0, 1),
                           bit abort     = 0,
                           bit en_ifetch = 0);
    uvm_status_e status;

    bit [TL_DW-1:0] data;
    bit [TL_AW-1:0] addr;
    tlul_pkg::tl_type_e tl_type;
    repeat (num_ops) begin
      // full randomize addr and data
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr)

      // never send InstrType transactions unless en_ifetch is enabled
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tl_type, !en_ifetch -> tl_type == tlul_pkg::DataType;)

      tl_access_w_abort(.addr(addr),
                        .data(data),
                        .status(status),
                        .mask(get_rand_contiguous_mask()),
                        .write($urandom_range(0, 1)),
                        .blocking(blocking),
                        .check_rsp(!en_ifetch),
                        .tl_type(tl_type),
                        .tl_sequencer_h(p_sequencer.sram_tl_sequencer_h),
                        .req_abort_pct((abort) ? 100 : 0));
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

endclass : sram_ctrl_base_vseq
