// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run OTP with reset
class flash_ctrl_otp_reset_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_otp_reset_vseq)
  `uvm_object_new
  typedef enum logic [10:0] {
    StIdle          = 11'b10001000001,
    StReqAddrKey    = 11'b01110101100,
    StReqDataKey    = 11'b01110010001,
    StReadSeeds     = 11'b11011111110,
    StReadEval      = 11'b01000100111,
    StWait          = 11'b00100111011,
    StEntropyReseed = 11'b00011000110,
    StRmaWipe       = 11'b10010110101,
    StRmaRsp        = 11'b10110001010,
    StDisabled      = 11'b11111100011,
    StInvalid       = 11'b11101011000
  } lc_ctrl_state_e;

  typedef enum {DVWaitAddrKey   = 0,
                DVWaitDataKey   = 1,
                DVWaitReadSeeds = 2,
                DVWait          = 3,
                DVWaitReadEval  = 4} reset_index_e;

  task body();
    int state_wait_timeout_ns = 10000; // 10 us
    fork begin
      fork
        begin
          csr_wr(.ptr(ral.init), .value(1));
          `uvm_info("Test","OTP",UVM_LOW)
          otp_model();
          `DV_SPINWAIT(wait(cfg.flash_ctrl_dv_vif.rd_buf_en == 1);,
                       "Timed out waiting for rd_buf_en",
                       state_wait_timeout_ns)
        end
        begin
          reset_index_e reset_index = $urandom_range(DVWaitAddrKey, DVWaitReadEval);
          `DV_SPINWAIT(wait(cfg.flash_ctrl_dv_vif.lcmgr_state == reset_index);,
                       $sformatf("Timed out waiting for %s", reset_index.name),
                       state_wait_timeout_ns)

          // Add extra cycles for longer states
          // to trigger reset in the middle of the state.
          if (reset_index == DVWaitAddrKey || reset_index == DVWaitDataKey) begin
            cfg.clk_rst_vif.wait_clks(2);
          end else if (reset_index == DVWaitReadSeeds || reset_index == DVWait) begin
            cfg.clk_rst_vif.wait_clks(10);
          end
          `uvm_info(`gfn, "RESET", UVM_LOW)
          cfg.seq_cfg.disable_flash_init = 1;
          // Enable secret seed at the beginning of the loop
          cfg.seq_cfg.en_init_keys_seeds = 0;
          apply_reset();
        end
      join_any
      disable fork;
      // Since the 2nd begin/end wait for substate of OTP,
      // the 2nd begin/end always finish first.
      // So diable fork only terminate first begin/end.
    end join // fork begin

    csr_wr(.ptr(ral.init), .value(1));
    `uvm_info("Test","OTP after loop",UVM_LOW)
    otp_model();
    `DV_SPINWAIT(wait(cfg.flash_ctrl_dv_vif.rd_buf_en == 1);,
                 "Timed out waiting for rd_buf_en",
                 state_wait_timeout_ns)
  endtask // body
endclass // flash_ctrl_otp_reset_vseq
