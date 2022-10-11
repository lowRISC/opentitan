// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controllber Arbiter for read
//

`include "prim_assert.sv"

// flash read and erase functionality is shared betewen the hardware (life cycle
// and key manager) and software interfaces.
//
// This module arbitrates and muxes the controls between the two interfaces.

module flash_ctrl_arb import flash_ctrl_pkg::*; (
  input clk_i,
  input rst_ni,

  input prim_mubi_pkg::mubi4_t disable_i,

  // error address shared between interfaces
  output logic [BusAddrW-1:0] ctrl_err_addr_o,

  // software interface to rd_ctrl / erase_ctrl
  input flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t sw_ctrl_i,
  input [BusAddrByteW-1:0] sw_addr_i,
  output logic sw_ack_o,
  output flash_ctrl_err_t sw_err_o,

  // software interface to prog_fifo
  input sw_wvalid_i,
  output logic sw_wready_o,
  input [BusFullWidth-1:0] sw_wdata_i,

  // hardware interface to rd_ctrl / erase_ctrl
  input hw_req_i,
  input flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t hw_ctrl_i,
  input flash_lcmgr_phase_e hw_phase_i,
  input [BusAddrByteW-1:0] hw_addr_i,
  output logic hw_ack_o,
  output flash_ctrl_err_t hw_err_o,

  // hardware interface to prog_fifo
  input hw_wvalid_i,
  input [BusFullWidth-1:0] hw_wdata_i,
  output logic hw_wready_o,

  // muxed interface to rd_ctrl / erase_ctrl
  output flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t muxed_ctrl_o,
  output logic [BusAddrByteW-1:0] muxed_addr_o,
  input prog_ack_i,
  input flash_ctrl_err_t prog_err_i,
  input [BusAddrW-1:0] prog_err_addr_i,
  input rd_ack_i,
  input flash_ctrl_err_t rd_err_i,
  input [BusAddrW-1:0] rd_err_addr_i,
  input erase_ack_i,
  input flash_ctrl_err_t erase_err_i,
  input [BusAddrW-1:0] erase_err_addr_i,

  // muxed interface to prog_fifo
  output logic prog_fifo_wvalid_o,
  output logic [BusFullWidth-1:0] prog_fifo_wdata_o,
  input logic prog_fifo_wready_i,

  // flash phy initialization ongoing
  input logic flash_phy_busy_i,

  // clear fifo contents
  output logic fifo_clr_o,

  // output to memory protection
  output flash_lcmgr_phase_e phase_o,

  // indication that sw has been selected
  output flash_sel_e sel_o,

  // fsm sparse error
  output logic fsm_err_o

);

  // arbitration FSM
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 5 -n 10 \
  //      -s 1044018132 --language=sv --avoid-zero
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (50.00%)
  //  6: |||||||||||||||| (40.00%)
  //  7: |||| (10.00%)
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 5
  // Maximum Hamming weight: 7
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StReset    = 10'b0011010110,
    StHw       = 10'b1111101110,
    StSwActive = 10'b1100101001,
    StSwIdle   = 10'b1000000010,
    StDisabled = 10'b0100010101
  } arb_state_e;

  flash_sel_e func_sel;
  arb_state_e state_q, state_d;

  logic sw_req;
  assign sw_req = sw_ctrl_i.start.q;

  // SEC_CM: CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, arb_state_e, StReset)

  always_comb begin

    func_sel = NoneSel;
    fifo_clr_o = 1'b0;
    state_d = state_q;
    fsm_err_o = 1'b0;

    unique case (state_q)
      StReset: begin
        // until the flash phy is done with its own iniitlization,
        // no flash controller activity is allowed to commence
        if (!flash_phy_busy_i) begin
          // after flash is ready, the HW interface always takes
          // precedence for flash control initiliazation
          state_d = StHw;
        end
      end

      StHw: begin
        func_sel = HwSel;

        if (!hw_req_i) begin
          state_d = StSwIdle;
        end
      end

      StSwIdle: begin
        // software is still selected to enable access to Fifos
        func_sel = SwSel;

        if (prim_mubi_pkg::mubi4_test_true_loose(disable_i)) begin
          // Do not randomly switch unless idle as it may cause stateful operations to be
          // disturbed
          state_d = StDisabled;
        end else if (hw_req_i) begin
          // if hardware request comes in the middle, wipe fifos and enable
          // switch to hardware interface
          fifo_clr_o = 1'b1;
          state_d = StHw;
        end else if (sw_req) begin
          state_d = StSwActive;
        end
      end

      StSwActive: begin
        func_sel = SwSel;

        // Stay in software active mode until operation completes.
        // While operations are ongoing, the interface cannot be switched
        if (prog_ack_i || rd_ack_i || erase_ack_i) begin
          state_d = StSwIdle;
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

  logic ctrl_ack;
  flash_ctrl_err_t ctrl_err;

  always_comb begin
    muxed_ctrl_o = '0;
    muxed_addr_o = '0;
    sw_ack_o = '0;
    sw_err_o = '0;
    sw_wready_o = '0;
    hw_ack_o = '0;
    hw_err_o = '0;

    hw_wready_o = '0;
    prog_fifo_wvalid_o = '0;
    prog_fifo_wdata_o = '0;

    unique case (func_sel)
      HwSel: begin
        // ctrl related muxing
        muxed_ctrl_o = hw_ctrl_i;
        muxed_addr_o = hw_addr_i;
        hw_ack_o = ctrl_ack;
        hw_err_o = ctrl_err;

        // fifo related muxing
        hw_wready_o = prog_fifo_wready_i;
        prog_fifo_wvalid_o = hw_wvalid_i;
        prog_fifo_wdata_o = hw_wdata_i;
      end

      SwSel: begin

        // ctrl related muxing
        muxed_ctrl_o = sw_ctrl_i;
        muxed_addr_o = sw_addr_i;
        sw_ack_o = ctrl_ack;
        sw_err_o = ctrl_err;

        // fifo related muxing
        sw_wready_o = prog_fifo_wready_i;
        prog_fifo_wvalid_o = sw_wvalid_i;
        prog_fifo_wdata_o = sw_wdata_i;
      end

      default:;
    endcase // unique case (func_sel)
  end

  // pick appropriate feedback
  always_comb begin
    ctrl_ack = '0;
    ctrl_err = '0;
    ctrl_err_addr_o = '0;

    unique case (muxed_ctrl_o.op.q)
      FlashOpProgram: begin
        ctrl_ack = prog_ack_i;
        ctrl_err = prog_err_i;
        ctrl_err_addr_o = prog_err_addr_i;
      end

      FlashOpErase: begin
        ctrl_ack = erase_ack_i;
        ctrl_err = erase_err_i;
        ctrl_err_addr_o = erase_err_addr_i;
      end

      FlashOpRead: begin
        ctrl_ack = rd_ack_i;
        ctrl_err = rd_err_i;
        ctrl_err_addr_o = rd_err_addr_i;
      end

      default: begin
        // if operation is started but does not match
        // any valid operation, error back
        if (muxed_ctrl_o.start) begin
          ctrl_ack = 1'b1;
          ctrl_err.invalid_op_err = 1'b1;
        end
      end

    endcase // unique case (muxed_ctrl_o.op.q)
  end

  assign sel_o = func_sel;

  // At the moment there is no software control indicating phase.
  assign phase_o = func_sel == SwSel ? PhaseInvalid : hw_phase_i;

endmodule // flash_ctrl_rd_arb
