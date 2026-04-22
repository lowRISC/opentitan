// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Controller Arbiter
// Arbitrates between two hardware interfaces (Lcmgr, OtpCtrl) and a software interface

`include "prim_assert.sv"

module rram_ctrl_arb
import rram_ctrl_pkg::*;
import rram_ctrl_reg_pkg::rram_ctrl_reg2hw_control_reg_t;
(
  input logic clk_i,
  input logic rst_ni,

  input  prim_mubi_pkg::mubi4_t         disable_i,
  // sw ctrl interface
  input  rram_ctrl_reg2hw_control_reg_t sw_ctrl_i,
  input  logic [BusAddrByteW-1:0]       sw_addr_i,
  output logic                          sw_done_o,
  output rram_ctrl_err_t                sw_err_o,
  // sw wr-fifo interface
  input  logic                          sw_wvalid_i,
  output logic                          sw_wready_o,
  input  logic [BusFullWidth-1:0]       sw_wdata_i,
  // sw rd-fifo interface
  input  logic                          sw_rready_i,
  output logic                          sw_rvalid_o,
  output logic [BusFullWidth-1:0]       sw_rdata_o,
  // hw-lcmgr ctrl interface
  input  logic                          hw_lcmgr_req_i,
  input  rram_ctrl_reg2hw_control_reg_t hw_lcmgr_ctrl_i,
  input  rram_phase_e                   hw_lcmgr_phase_i,
  input  logic [BusAddrByteW-1:0]       hw_lcmgr_addr_i,
  output logic                          hw_lcmgr_done_o,
  output rram_ctrl_err_t                hw_lcmgr_err_o,
  // hw-lcmgr wr-fifo interface
  input  logic                          hw_lcmgr_wvalid_i,
  input  logic [BusFullWidth-1:0]       hw_lcmgr_wdata_i,
  output logic                          hw_lcmgr_wready_o,
  // hw-lcmgr read interface
  input  logic                          hw_lcmgr_rready_i,
  output logic [BusFullWidth-1:0]       hw_lcmgr_rdata_o,
  output logic                          hw_lcmgr_rvalid_o,
  // hw-otp ctrl interface
  input  logic                          hw_otp_req_i,
  input  rram_ctrl_reg2hw_control_reg_t hw_otp_ctrl_i,
  input  logic [BusAddrByteW-1:0]       hw_otp_addr_i,
  output logic                          hw_otp_done_o,
  output rram_ctrl_err_t                hw_otp_err_o,
  // hw-otp wr-fifo interface
  input  logic                          hw_otp_wvalid_i,
  input  logic [BusFullWidth-1:0]       hw_otp_wdata_i,
  output logic                          hw_otp_wready_o,
  // hw-otp read interface
  input  logic                          hw_otp_rready_i,
  output logic [BusFullWidth-1:0]       hw_otp_rdata_o,
  output logic                          hw_otp_rvalid_o,
  // Control to wr/rd handler
  output rram_part_e                    ctrl_part_o,
  output logic [CtrlMaxWordsW-1:0]      ctrl_num_words_o,
  output logic                          wr_op_start_o,
  output logic [BusAddrW-1:0]           wr_op_addr_o,
  output logic                          rd_op_start_o,
  output logic [BusAddrW-1:0]           rd_op_addr_o,
  // Response from wr/rd handler
  input  logic                          wr_done_i,
  input  rram_ctrl_err_t                wr_err_i,
  input  logic [BusAddrW-1:0]           wr_err_addr_i,
  input  logic                          rd_done_i,
  input  rram_ctrl_err_t                rd_err_i,
  input  logic [BusAddrW-1:0]           rd_err_addr_i,
  input  logic [BusFullWidth-1:0]       rd_ctrl_rdata_i,
  input  logic                          rd_ctrl_rvalid_i,
  output logic                          rd_ctrl_rready_o,
  // Muxed interface to wr_fifo
  output logic                          wr_fifo_wvalid_o,
  output logic [BusFullWidth-1:0]       wr_fifo_wdata_o,
  input  logic                          wr_fifo_wready_i,
  output logic                          wr_fifo_clr_o,
  // Control and status signals
  input  logic                          ctrl_init_done_i,
  input  logic                          phy_init_done_i,
  output rram_sel_e                     if_sel_o,
  output rram_phase_e                   phase_o,
  output logic [BusAddrW-1:0]           ctrl_err_addr_o,
  output logic                          fsm_err_o
);

  // arbitration FSM
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 8 -n 10 \
  //     -s 239575134 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (53.57%)
  //  6: ||||||||||||| (35.71%)
  //  7: | (3.57%)
  //  8: || (7.14%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 7
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StReset     = 10'b1101000001,
    StHwOtp     = 10'b0001111100,
    StHwLcmgr   = 10'b0100010110,
    StSw        = 10'b0111100111,
    StIdle      = 10'b0011011011,
    StRewriteRd = 10'b1010000010,
    StRewriteWr = 10'b1110101100,
    StDisabled  = 10'b1100111011
  } arb_state_e;
  arb_state_e state_d, state_q;

  rram_ctrl_reg2hw_control_reg_t muxed_ctrl;
  logic [BusAddrByteW-1:0]       muxed_addr;
  logic                          sw_req;
  rram_sel_e                     if_sel;

  // Rewrite signals
  logic [BusAddrByteW-1:0]       rw_addr_q, rw_addr_d;
  rram_part_e                    rw_part_q, rw_part_d;
  rram_ctrl_reg2hw_control_reg_t rw_ctrl;
  logic                          rw_ctrl_done;
  rram_ctrl_err_t                rw_ctrl_err;
  logic                          rw_sw_req;

  assign sw_req    = sw_ctrl_i.start.q & (sw_ctrl_i.op.q != RramOpRewrite);
  assign rw_sw_req = sw_ctrl_i.start.q & (sw_ctrl_i.op.q == RramOpRewrite);

  // SEC_CM: CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, arb_state_e, StReset)

  // store request data
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rw_addr_q <= '0;
      rw_part_q <= RramPartData;
    end else begin
      rw_addr_q <= rw_addr_d;
      rw_part_q <= rw_part_d;
    end
  end

  always_comb begin
    if_sel        = NoneSel;
    wr_fifo_clr_o = 1'b0;
    state_d       = state_q;
    fsm_err_o     = 1'b0;
    rw_addr_d     = rw_addr_q;
    rw_part_d     = rw_part_q;
    rw_ctrl       = '0;
    rw_ctrl_done  = '0;
    rw_ctrl_err   = '0;

    unique case (state_q)
      StReset: begin
        // Until the rram phy is done with its own initialization,
        // the RRAM cannot be accessed
        if (phy_init_done_i) begin
          state_d = StIdle;
        end
      end

      StHwLcmgr: begin
        if_sel = HwLcMgrSel;
        // HW-interface relies on back to back operations without rearbitration
        if (!hw_lcmgr_req_i) begin
          state_d = StIdle;
        end
      end

      StHwOtp: begin
        if_sel = HwOtpSel;
        // HW-interface relies on back to back operations without rearbitration
        if (!hw_otp_req_i) begin
          state_d = StIdle;
        end
      end

      StIdle: begin
        // Software is still selected to enable access to FIFOs
        if (ctrl_init_done_i) if_sel = SwSel;

        if (prim_mubi_pkg::mubi4_test_true_loose(disable_i)) begin
          // Do not randomly switch unless idle as it may cause stateful operations to be
          // disturbed
          state_d = StDisabled;
        end else if (hw_otp_req_i | hw_lcmgr_req_i) begin
          // if hardware interfaces are selected, wipe fifos and enable it
          // switch to hardware interface
          wr_fifo_clr_o = 1'b1;
          // priority is given to the OTP interface
          state_d = hw_otp_req_i ? StHwOtp : StHwLcmgr;
        end else if (sw_req & ctrl_init_done_i) begin
          // clear wr_fifo upon new request
          wr_fifo_clr_o = 1'b1;
          state_d       = StSw;
        end else if (rw_sw_req & ctrl_init_done_i) begin
          // Clear wr_fifo upon new request
          wr_fifo_clr_o = 1'b1;
          rw_addr_d     = sw_addr_i;
          rw_part_d     = rram_part_e'(sw_ctrl_i.partition.q);
          state_d       = StRewriteRd;
        end
      end

      StSw: begin
        if_sel = SwSel;

        // Stay in software active mode until operation completes.
        // While operations are ongoing, the interface cannot be switched
        if (wr_done_i || rd_done_i) begin
          state_d = StIdle;
        end
      end

      // Send a read request
      StRewriteRd: begin
        if_sel = HwLoopBack;

        rw_ctrl.num.q       = WidthMultiple - 1;
        rw_ctrl.partition.q = rw_part_q;
        rw_ctrl.op.q        = RramOpRead;
        rw_ctrl.start.q     = 1'b1;

        if (rd_done_i) begin
          if (rd_err_i != '0) begin
            rw_ctrl_done = 1'b1;
            rw_ctrl_err  = rd_err_i;
            state_d      = StIdle;
          end else begin
            state_d = StRewriteWr;
          end
        end
      end

      // Send a write request with the received data
      StRewriteWr: begin
        if_sel = HwLoopBack;

        rw_ctrl.num.q       = WidthMultiple - 1;
        rw_ctrl.partition.q = rw_part_q;
        rw_ctrl.op.q        = RramOpWrite;
        rw_ctrl.start.q     = 1'b1;

        if (wr_done_i) begin
          state_d      = StIdle;
          rw_ctrl_done = 1'b1;
          rw_ctrl_err  = wr_err_i;
        end
      end

      StDisabled: begin
        state_d = StDisabled;
      end

      default: begin
        fsm_err_o = 1'b1;
      end
    endcase // unique case (state_q)
  end // always_comb

  logic           ctrl_done;
  rram_ctrl_err_t ctrl_err;

  // ctrl interface selection based in if_sel
  always_comb begin
    muxed_ctrl = '0;
    muxed_addr = '0;

    sw_done_o   = '0;
    sw_err_o    = '0;
    sw_wready_o = '0;
    sw_rvalid_o = '0;
    sw_rdata_o  = '0;

    hw_otp_done_o   = '0;
    hw_otp_err_o    = '0;
    hw_otp_rdata_o  = '0;
    hw_otp_rvalid_o = '0;

    hw_lcmgr_done_o   = '0;
    hw_lcmgr_err_o    = '0;
    hw_lcmgr_rdata_o  = '0;
    hw_lcmgr_rvalid_o = '0;

    hw_otp_wready_o   = '0;
    hw_lcmgr_wready_o = '0;
    wr_fifo_wvalid_o  = '0;
    wr_fifo_wdata_o   = '0;
    rd_ctrl_rready_o  = 1'b0;

    phase_o = PhaseInvalid;

    unique case (if_sel)
      HwOtpSel: begin
        // ctrl related muxing
        muxed_ctrl      = hw_otp_ctrl_i;
        muxed_addr      = hw_otp_addr_i;
        hw_otp_done_o   = ctrl_done;
        hw_otp_err_o    = ctrl_err;
        hw_otp_rvalid_o = rd_ctrl_rvalid_i;
        hw_otp_rdata_o  = rd_ctrl_rdata_i;

        // fifo related muxing
        hw_otp_wready_o  = wr_fifo_wready_i;
        wr_fifo_wvalid_o = hw_otp_wvalid_i;
        wr_fifo_wdata_o  = hw_otp_wdata_i;

        rd_ctrl_rready_o = hw_otp_rready_i;
      end

      HwLcMgrSel: begin
        // ctrl related muxing
        muxed_ctrl        = hw_lcmgr_ctrl_i;
        muxed_addr        = hw_lcmgr_addr_i;
        hw_lcmgr_done_o   = ctrl_done;
        hw_lcmgr_err_o    = ctrl_err;
        hw_lcmgr_rvalid_o = rd_ctrl_rvalid_i;
        hw_lcmgr_rdata_o  = rd_ctrl_rdata_i;

        // fifo related muxing
        hw_lcmgr_wready_o = wr_fifo_wready_i;
        wr_fifo_wvalid_o  = hw_lcmgr_wvalid_i;
        wr_fifo_wdata_o   = hw_lcmgr_wdata_i;

        rd_ctrl_rready_o = hw_lcmgr_rready_i;

        phase_o = hw_lcmgr_phase_i;
      end

      SwSel: begin
        muxed_ctrl  = sw_ctrl_i;
        muxed_addr  = sw_addr_i;
        sw_done_o   = ctrl_done;
        sw_err_o    = ctrl_err;
        sw_rvalid_o = rd_ctrl_rvalid_i;
        sw_rdata_o  = rd_ctrl_rdata_i;

        // fifo related muxing
        sw_wready_o      = wr_fifo_wready_i;
        wr_fifo_wvalid_o = sw_wvalid_i;
        wr_fifo_wdata_o  = sw_wdata_i;

        rd_ctrl_rready_o = sw_rready_i;
      end

      HwLoopBack: begin
        muxed_ctrl = rw_ctrl;
        muxed_addr = rw_addr_q;

        sw_done_o = rw_ctrl_done;
        sw_err_o  = rw_ctrl_err;

        // write read response to wr-fifo
        wr_fifo_wvalid_o = rd_ctrl_rvalid_i;
        wr_fifo_wdata_o  = rd_ctrl_rdata_i;

        rd_ctrl_rready_o = wr_fifo_wready_i;
      end
      default:;
    endcase // unique case (if_sel)
  end

  // Response selection based on operation
  always_comb begin
    ctrl_done       = '0;
    ctrl_err        = '0;
    ctrl_err_addr_o = '0;

    unique case (muxed_ctrl.op.q)
      RramOpWrite: begin
        ctrl_done       = wr_done_i;
        ctrl_err        = wr_err_i;
        ctrl_err_addr_o = wr_err_addr_i;
      end

      RramOpRead: begin
        ctrl_done       = rd_done_i;
        ctrl_err        = rd_err_i;
        ctrl_err_addr_o = rd_err_addr_i;
      end

      RramOpRewrite: begin
        ctrl_err_addr_o = (rw_ctrl_err == '0) ? '0 : rw_addr_q[BusByteWidth +: BusAddrW];
      end

      default: begin
        // if operation is started but does not match
        // any valid operation, error back
        if (muxed_ctrl.start.q) begin
          ctrl_done               = 1'b1;
          ctrl_err.invalid_op_err = 1'b1;
        end
      end
    endcase // unique case (muxed_ctrl.op.q)
  end

  assign ctrl_part_o      = rram_part_e'(muxed_ctrl.partition.q);
  assign ctrl_num_words_o = muxed_ctrl.num.q;
  assign wr_op_start_o    = muxed_ctrl.start.q & (muxed_ctrl.op.q == RramOpWrite);
  assign wr_op_addr_o     = muxed_addr[BusByteWidth +: BusAddrW];
  assign rd_op_start_o    = muxed_ctrl.start.q & (muxed_ctrl.op.q == RramOpRead);
  assign rd_op_addr_o     = muxed_addr[BusByteWidth +: BusAddrW];

  assign if_sel_o = if_sel;

  // Byte-offset bits of muxed_addr are not consumed (word-addressed operations only)
  logic unused_muxed_addr;
  assign unused_muxed_addr = ^muxed_addr[BusByteWidth-1:0];

endmodule // rram_ctrl_arb
