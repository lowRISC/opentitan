// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_base_vseq #(parameter int AddrWidth = `SRAM_ADDR_WIDTH) extends cip_base_vseq #(
    .RAL_T               (sram_ctrl_regs_reg_block),
    .CFG_T               (sram_ctrl_env_cfg#(AddrWidth)),
    .COV_T               (sram_ctrl_env_cov#(AddrWidth)),
    .VIRTUAL_SEQUENCER_T (sram_ctrl_virtual_sequencer#(AddrWidth))
  );
  `uvm_object_param_utils(sram_ctrl_base_vseq#(AddrWidth))
  `uvm_object_new

  // various knobs to enable certain routines
  bit do_sram_ctrl_init = 1'b1;

  bit stress_pipeline = 1'b0;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_sram_ctrl_init) sram_ctrl_init();
  endtask

  virtual task apply_reset(string kind = "HARD");
    cfg.lc_vif.init();
    super.apply_reset(kind);
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
    ral.ctrl.renew_scr_key.set(1);
    ral.ctrl.init.set(1);
    csr_update(.csr(ral.ctrl));
    csr_spinwait(.ptr(ral.status.init_done), .exp_data(1));

    // initialize mem_model
    cfg.scb.init_mem();
  endtask

  // Request a new scrambling key from the OTP interface.
  //
  // Will trigger a request to the KDI push_pull agent.
  virtual task req_scr_key();
    ral.ctrl.renew_scr_key.set(1);
    csr_update(.csr(ral.ctrl));
    csr_spinwait(.ptr(ral.status.scr_key_valid), .exp_data(1));

    // initialize mem_model
    cfg.scb.init_mem();
  endtask

  // Task to perform a single SRAM read at the specified location
  virtual task do_single_read(input bit [TL_AW-1:0]    addr,
                              input bit [TL_DBW-1:0]   mask         = get_rand_contiguous_mask(),
                              input bit                blocking     = $urandom_range(0, 1),
                              input bit                check_rdata  = 0,
                              input bit [TL_DW-1:0]    exp_rdata    = '0,
                              input mubi4_t            instr_type   = MuBi4False,
                              output logic [TL_DW-1:0] rdata);
    tl_access(.addr(addr),
              .data(rdata),
              .mask(mask),
              .write(1'b0),
              .blocking(blocking),
              .check_exp_data(check_rdata),
              .exp_data(exp_rdata),
              .compare_mask(mask),
              .instr_type(instr_type),
              .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]));
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // Task to perform a single SRAM write at the specified location
  virtual task do_single_write(bit [TL_AW-1:0]  addr,
                               bit [TL_DW-1:0]  data,
                               bit [TL_DBW-1:0] mask        = get_rand_contiguous_mask(),
                               bit              blocking    = $urandom_range(0, 1),
                               mubi4_t          instr_type  = MuBi4False);
    tl_access(.addr(addr),
              .data(data),
              .mask(mask),
              .write(1'b1),
              .blocking(blocking),
              .instr_type(instr_type),
              .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]));
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // This task is designed to kick off `num_stress_ops` back to back memory transactions
  // to the same address, to stress the SRAM pipelining implementation
  virtual task do_stress_ops(bit [TL_AW-1:0] addr,
                             int num_stress_ops,
                             bit en_ifetch = 0);
    bit [TL_DW-1:0] data;
    mubi4_t instr_type;

    repeat (num_stress_ops) begin
      // fully randomize data
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)

      // never send InstrType transactions unless en_ifetch is enabled
      if (en_ifetch) instr_type = get_rand_mubi4_val();
      else           instr_type = MuBi4False;

      tl_access(.addr(addr),
                .data(data),
                .mask(get_rand_contiguous_mask()),
                .write($urandom_range(0, 1)),
                .check_rsp(!en_ifetch),
                .blocking(1'b0),
                .instr_type(instr_type),
                .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]));
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
    bit [TL_DW-1:0] data;
    bit [TL_AW-1:0] addr;
    mubi4_t instr_type;
    repeat (num_ops) begin
      bit completed, saw_err;

      // full randomize addr and data
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr)

      // never send InstrType transactions unless en_ifetch is enabled
      if (en_ifetch) instr_type = get_rand_mubi4_val();
      else           instr_type = MuBi4False;

      tl_access_w_abort(.addr(addr),
                        .data(data),
                        .completed(completed),
                        .saw_err(saw_err),
                        .mask(get_rand_contiguous_mask()),
                        .write($urandom_range(0, 1)),
                        .blocking(blocking),
                        .check_rsp(!en_ifetch),
                        .instr_type(instr_type),
                        .tl_sequencer_h(p_sequencer.tl_sequencer_hs[cfg.sram_ral_name]),
                        .req_abort_pct((abort) ? 100 : 0));
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

endclass : sram_ctrl_base_vseq
