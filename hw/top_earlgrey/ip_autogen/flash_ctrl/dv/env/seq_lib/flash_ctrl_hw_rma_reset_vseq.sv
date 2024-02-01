// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run rma request event with random resets
class flash_ctrl_hw_rma_reset_vseq extends flash_ctrl_hw_rma_vseq;

// Observed wait time for each state:
// DVStRmaPageSel    : 0.120 us
// DVStRmaErase      : 0.140 us
// DVStRmaEraseWait  : 6.065 us
// DVStRmaWordSel    : 6.088 us
// DVStRmaProgram    : 2.776 us
// DVStRmaProgramWait: 2.797 us
// DVStRmaRdVerify   : 3.464 us
// RMA : 108 msec
  typedef enum {DVStRmaPageSel     = 0,
                DVStRmaErase       = 1,
                DVStRmaEraseWait   = 2,
                DVStRmaWordSel     = 3,
                DVStRmaProgram     = 4,
                DVStRmaProgramWait = 5,
                DVStRmaRdVerify    = 6} reset_state_index_e;
  `uvm_object_utils(flash_ctrl_hw_rma_reset_vseq)
  `uvm_object_new

  task pre_start();
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = lc_ctrl_pkg::On;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = lc_ctrl_pkg::On;
    cfg.seq_cfg.en_init_keys_seeds = 1;
    super.pre_start();
  endtask

  task body();
    logic [RmaSeedWidth-1:0] rma_seed;
    bit                      rma_done = 0;
    bit                      flash_dis = 0;
    // INITIALIZE FLASH REGIONS
    init_data_part();
    init_info_part();
    flash_dis = $urandom();

    fork begin
      // SEND RMA REQUEST (Erases the Flash and Writes Random Data To All Partitions)
      fork
        begin
          `uvm_info("Test", $sformatf("RMA REQUEST flash_dis:%0d", flash_dis), UVM_LOW)
          rma_seed = $urandom;  // Random RMA Seed
          send_rma_req(rma_seed);
          rma_done = 1;
        end
        begin
          reset_state_index_e reset_state_index = reset_state_index_e'(
                                                  $urandom_range(DVStRmaPageSel, DVStRmaRdVerify));
          // Assert reset during RMA state transition
          `uvm_info("Test", $sformatf("Reset index: %s", reset_state_index.name), UVM_LOW)
          `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rma_state == dv2rma_st(reset_state_index));,
                       $sformatf("Timed out waiting for rma_state: %s", reset_state_index.name),
                       cfg.seq_cfg.state_wait_timeout_ns)
          // Give more cycles for long stages
          // to trigger reset in the middle of the state.
          if (reset_state_index inside {StRmaRdVerify, StRmaErase}) cfg.clk_rst_vif.wait_clks(10);

          if (flash_dis) begin
            `uvm_info("Test", "set disable_flash", UVM_MEDIUM)
            cfg.scb_h.do_alert_check = 0;
            update_assert(.enable(0));
            csr_wr(.ptr(ral.dis), .value(get_rand_mubi4_val(.f_weight(0))));
            cfg.clk_rst_vif.wait_clks(10);
          end
          `uvm_info("Test", "RESET", UVM_LOW)
          lc_ctrl_if_rst();  // Restore lc_ctrl_if to Reset Values
          apply_reset();
        end
      join_any
      disable fork;
      // Since the 2nd begin/end wait for substate of RMA,
      // the 2nd begin/end always finish first.
      // So diable fork only terminate send_rma_req.
    end join // fork begin

    `uvm_info("Test", "RMA END", UVM_LOW)
    `DV_CHECK_NE(rma_done, 1, "rma_done shouldn't be 1")
    if (rma_done == 0) begin
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

      update_assert(.enable(1));
      // INITIALIZE FLASH REGIONS
      init_data_part();
      init_info_part();
      `uvm_info("Test", "RMA REQUEST", UVM_LOW)
      rma_seed = $urandom;  // Random RMA Seed
      send_rma_req(rma_seed);
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

      // CHECK HOST SOFTWARE HAS NO ACCESS TO THE FLASH
      // Attempt to Read from FLASH Controller
      do_flash_ctrl_access_check();
    end // if (rma_done == 0)
  endtask

  function rma_state_e dv2rma_st(reset_state_index_e idx);
    case (idx)
      DVStRmaPageSel: return StRmaPageSel;
      DVStRmaErase: return StRmaErase;
      DVStRmaEraseWait: return StRmaEraseWait;
      DVStRmaWordSel: return StRmaWordSel;
      DVStRmaProgram: return StRmaProgram;
      DVStRmaProgramWait: return StRmaProgramWait;
      DVStRmaRdVerify: return StRmaRdVerify;
      default: begin
        `uvm_error("dv2rma_st", $sformatf("unknown index:%0d", idx))
      end
    endcase
  endfunction // dv2rma_st

  function void update_assert(bit enable);
    if (enable) begin
      $asserton(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");
      $asserton(0, "tb.dut.u_flash_hw_if.u_addr_sync_reqack.SyncReqAckHoldReq");
      $asserton(0, "tb.dut.u_flash_hw_if.ProgRdVerify_A");
    end else begin
      $assertoff(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");
      $assertoff(0, "tb.dut.u_flash_hw_if.u_addr_sync_reqack.SyncReqAckHoldReq");
      $assertoff(0, "tb.dut.u_flash_hw_if.ProgRdVerify_A");
    end
  endfunction // update_assert
endclass // flash_ctrl_hw_rma_reset_vseq
