// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run OTP with reset and other misbehavior to stretch coverage
class flash_ctrl_otp_reset_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_otp_reset_vseq)
  `uvm_object_new
  typedef enum logic [10:0] {
    StIdle          = 11'b10001000001,  //
    StReqAddrKey    = 11'b01110101100,  // 0.615 us
    StReqDataKey    = 11'b01110010001,  // 0.775
    StReadSeeds     = 11'b11011111110,  // 0.934
    StReadEval      = 11'b01000100111,  // 3.032
    StWait          = 11'b00100111011,  // 4.856
    StEntropyReseed = 11'b00011000110,  // 4.947
    StRmaWipe       = 11'b10010110101,  // 4.97
    StRmaRsp        = 11'b10110001010,  // 3093.344
    StDisabled      = 11'b11111100011,  //
    StInvalid       = 11'b11101011000   //
  } lc_ctrl_state_e;

  typedef enum {
                DVWaitAddrKey   = 0,
                DVWaitDataKey   = 1,
                DVWaitReadSeeds = 2,
                DVWaitReadEval  = 3,
                DVWait          = 4,
                DVWaitEntropyReseed = 5,
                DVWaitRmaWipe       = 6,
                DVWaitRmaRsp        = 7
                } reset_index_e;


  task pre_start();
    cfg.skip_init = 1;
    super.pre_start();
  endtask

  task body();
    int long_wait_timeout_ns = 5000000; // 5ms
    int wait_time;
    string path;
    logic [RmaSeedWidth-1:0] rma_seed;
     cfg.scb_h.do_alert_check = 0;

    repeat(4) begin
      update_assert(.enable(0));
      fork begin
        fork
          begin
            csr_wr(.ptr(ral.init), .value(1));
            `uvm_info("Test","OTP",UVM_LOW)
            otp_model();
            `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rd_buf_en == 1);,
                         "Timed out waiting for rd_buf_en",
                         cfg.seq_cfg.state_wait_timeout_ns)
            `uvm_info("Test", "RMA REQUEST START", UVM_LOW)
            rma_seed = $urandom;  // Random RMA Seed
            send_rma_req(rma_seed);
            `uvm_info("Test", "RMA REQUEST DONE", UVM_LOW)

            cfg.flash_ctrl_vif.rma_req <= lc_ctrl_pkg::Off;
          end
          begin
            // exceptions
            // 0. none
            // 1. add disable to each state
            // 2. rma_req[1] == true at StReqAddrKey, StReqDataKey
            // 3. StReqDataKey, data_key_ack_q = 1, provision_en_i = 0
            bit[1:0] exception_mode;
            reset_index_e reset_index = reset_index_e'($urandom_range(DVWaitAddrKey,
                                                                      DVWaitEntropyReseed));
            `DV_CHECK_STD_RANDOMIZE_FATAL(exception_mode)

            `uvm_info("Test", $sformatf("index: %s exception_mode: %0d",
                                        reset_index.name, exception_mode), UVM_LOW)
            if (reset_index == DVWaitRmaRsp) wait_time = long_wait_timeout_ns;
            else wait_time = cfg.seq_cfg.state_wait_timeout_ns;

            `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.lcmgr_state == dv2rtl_st(reset_index));,
                         $sformatf("Timed out waiting for %s", reset_index.name),
                         wait_time)
            // Since these are single cycle state,
            // use force for disable or reset
            if (reset_index == DVWaitReadEval || reset_index == DVWaitEntropyReseed)begin
              @(negedge cfg.clk_rst_vif.clk);

              if (exception_mode[0]) begin
                // disable
                path = "tb.dut.u_flash_hw_if.disable_i";
                `DV_CHECK(uvm_hdl_force(path, MuBi4True))
              end else begin
                // reset
                path = "tb.dut.u_flash_hw_if.rst_ni";
                `DV_CHECK(uvm_hdl_force(path, 0))
              end
              cfg.clk_rst_vif.wait_clks(2);
              `DV_CHECK(uvm_hdl_release(path))
            end else begin
              // Add extra cycles for longer states
              // to trigger reset in the middle of the state.
              if (reset_index == DVWaitAddrKey || reset_index == DVWaitDataKey) begin
                cfg.clk_rst_vif.wait_clks(2);
              end else if (reset_index == DVWaitReadSeeds || reset_index == DVWait) begin
                cfg.clk_rst_vif.wait_clks(10);
              end
              case(exception_mode)
                2'b01: begin
                  csr_wr(.ptr(ral.dis), .value(get_rand_mubi4_val(.f_weight(0))));
                end
                2'b10: begin
                  if (reset_index inside {DVWaitAddrKey, DVWaitDataKey}) begin
                    cfg.flash_ctrl_vif.rma_req <= lc_ctrl_pkg::On;
                    cfg.clk_rst_vif.wait_clks(2);
                    cfg.flash_ctrl_vif.rma_req <= lc_ctrl_pkg::Off;
                  end
                end
                2'b11: begin
                  if (reset_index == DVWaitDataKey) begin
                    cfg.flash_ctrl_vif.lc_seed_hw_rd_en =
                      get_rand_lc_tx_val(.t_weight(0), .f_weight(1), .other_weight(9));
                  end
                end
                default: begin
                  // Add no disturbance.
                end
              endcase
              cfg.clk_rst_vif.wait_clks(10);
            end
            `uvm_info(`gfn, "RESET", UVM_LOW)
            // Enable secret seed at the beginning of the loop
            cfg.seq_cfg.en_init_keys_seeds = 0;
            cfg.flash_ctrl_vif.rma_req = lc_ctrl_pkg::Off;
            apply_reset();
          end
        join_any
        disable fork;
        // Since the 2nd begin/end wait for substate of OTP,
        // the 2nd begin/end always finish first.
        // So diable fork only terminate first begin/end.
      end join // fork begin

      update_assert(.enable(1));
      csr_wr(.ptr(ral.init), .value(1));
      cfg.clk_rst_vif.wait_clks(2);
      `uvm_info("Test","OTP after loop",UVM_LOW)
      otp_model();
      `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rd_buf_en == 1);,
                   "Timed out waiting for rd_buf_en",
                   cfg.seq_cfg.state_wait_timeout_ns)

      apply_reset();
      cfg.flash_ctrl_vif.lc_seed_hw_rd_en = lc_ctrl_pkg::On;
    end
  endtask // body

  function lc_ctrl_state_e dv2rtl_st(reset_index_e idx);
    case (idx)
      DVWaitAddrKey: return StReqAddrKey;
      DVWaitDataKey: return StReqDataKey;
      DVWaitReadSeeds: return StReadSeeds;
      DVWait: return StWait;
      DVWaitReadEval: return StReadEval;
      DVWaitEntropyReseed: return StEntropyReseed;
      DVWaitRmaWipe: return StRmaWipe;
      DVWaitRmaRsp: return StRmaRsp;
      default: begin
        `uvm_error("dv2rma_st", $sformatf("unknown index:%0d", idx))
      end
    endcase
  endfunction
  function void update_assert(bit enable);
    if (enable) begin
      $asserton(0, "tb.dut.u_flash_hw_if.u_addr_sync_reqack.SyncReqAckHoldReq");
      $asserton(0, "tb.dut.u_flash_hw_if.u_data_sync_reqack.SyncReqAckHoldReq");
      $asserton(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");
    end else begin
      $assertoff(0, "tb.dut.u_flash_hw_if.u_addr_sync_reqack.SyncReqAckHoldReq");
      $assertoff(0, "tb.dut.u_flash_hw_if.u_data_sync_reqack.SyncReqAckHoldReq");
      $assertoff(0, "tb.dut.u_flash_mp.NoReqWhenErr_A");
    end
  endfunction
endclass // flash_ctrl_otp_reset_vseq
