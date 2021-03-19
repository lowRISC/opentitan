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

  // software interface to rd_ctrl / erase_ctrl
  input flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t sw_ctrl_i,
  input [31:0] sw_addr_i,
  output logic sw_ack_o,
  output logic sw_err_o,

  // software interface to rd_fifo
  output logic sw_rvalid_o,
  input sw_rready_i,

  // software interface to prog_fifo
  input sw_wvalid_i,
  output logic sw_wready_o,
  input [BusWidth-1:0] sw_wdata_i,

  // hardware interface to rd_ctrl / erase_ctrl
  input hw_req_i,
  input flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t hw_ctrl_i,
  input flash_lcmgr_phase_e hw_phase_i,
  input [31:0] hw_addr_i,
  output logic hw_ack_o,
  output logic hw_err_o,

  // hardware interface to rd_fifo
  output logic hw_rvalid_o,
  input hw_rready_i,

  // hardware interface to prog_fifo
  input hw_wvalid_i,
  input [BusWidth-1:0] hw_wdata_i,
  output logic hw_wready_o,

  // muxed interface to rd_ctrl / erase_ctrl
  output flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t muxed_ctrl_o,
  output logic [31:0] muxed_addr_o,
  input prog_ack_i,
  input prog_err_i,
  input rd_ack_i,
  input rd_err_i,
  input erase_ack_i,
  input erase_err_i,

  // muxed interface to rd_fifo
  input rd_fifo_rvalid_i,
  output logic rd_fifo_rready_o,

  // muxed interface to prog_fifo
  output logic prog_fifo_wvalid_o,
  output logic [BusWidth-1:0] prog_fifo_wdata_o,
  input logic prog_fifo_wready_i,

  // flash phy initialization ongoing
  input logic flash_phy_busy_i,

  // clear fifo contents
  output logic fifo_clr_o,

  // output to memory protection
  output flash_lcmgr_phase_e phase_o,

  // indication that sw has been selected
  output flash_sel_e sel_o

);

  // arbitration FSM
  typedef enum logic [1:0] {
    StReset,  // at reset wait for flash phy to be ready
    StHw,
    StSwActive,
    StSwIdle
  } state_e;

  flash_sel_e func_sel;
  state_e state_q, state_d;

  logic sw_req;
  assign sw_req = sw_ctrl_i.start.q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StReset;
    end else begin
      state_q <= state_d;
    end
  end

  always_comb begin

    func_sel = NoneSel;
    fifo_clr_o = 1'b0;
    state_d = state_q;

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

        // if hardware request comes in the middle, wipe fifos and enable
        // switch to hardware interface
        if (hw_req_i) begin
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

      default:;
    endcase // unique case (state_q)
  end // always_comb

  logic ctrl_ack, ctrl_err;

  always_comb begin
    muxed_ctrl_o = '0;
    muxed_addr_o = '0;
    sw_ack_o = 1'b0;
    sw_err_o = 1'b0;
    sw_rvalid_o = 1'b0;
    sw_wready_o = 1'b0;
    hw_ack_o = 1'b0;
    hw_err_o = 1'b0;
    hw_rvalid_o = 1'b0;
    hw_wready_o = 1'b0;
    prog_fifo_wvalid_o = 1'b0;
    prog_fifo_wdata_o = '0;
    rd_fifo_rready_o = 1'b0;

    unique case (func_sel)
      HwSel: begin
        // ctrl related muxing
        muxed_ctrl_o = hw_ctrl_i;
        muxed_addr_o = hw_addr_i;
        hw_ack_o = ctrl_ack;
        hw_err_o = ctrl_err;

        // fifo related muxing
        hw_rvalid_o = rd_fifo_rvalid_i;
        hw_wready_o = prog_fifo_wready_i;
        rd_fifo_rready_o = hw_rready_i;
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
        sw_rvalid_o = rd_fifo_rvalid_i;
        sw_wready_o = prog_fifo_wready_i;
        rd_fifo_rready_o = sw_rready_i;
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
    if (muxed_ctrl_o.op.q == FlashOpProgram) begin
      ctrl_ack = prog_ack_i;
      ctrl_err = prog_err_i;
    end else if (muxed_ctrl_o.op.q == FlashOpErase) begin
      ctrl_ack = erase_ack_i;
      ctrl_err = erase_err_i;
    end else if (muxed_ctrl_o.op.q == FlashOpRead) begin
      ctrl_ack = rd_ack_i;
      ctrl_err = rd_err_i;
    end
  end

  assign sel_o = func_sel;

  // At the moment there is no software control indicating phase.
  assign phase_o = func_sel == SwSel ? PhaseInvalid : hw_phase_i;

endmodule // flash_ctrl_rd_arb
