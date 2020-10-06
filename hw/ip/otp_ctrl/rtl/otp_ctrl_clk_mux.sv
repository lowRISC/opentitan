// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is the OTP clock mux module. It basically implements a glitchless clock mux to
// switch the OTP macro from the standard clock clk_i to the clk_raw_i to be used for RAW
// unlock, where the standard clock clk_i has not been calibrated yet.
//
// There are however a couple of peculiarities to this block that should be noted:
//
// 1) The clock mux only supports switching in one direction. I.e., once the clock has been
//    switched from clk_i to clk_raw_i, a system reset is required to set the mux back to clk_i.
// 2) The FSM and the mux enable signal lc_raw_clk_en_i are both redundantly encoded, in order
//    to make it hard to glitch the clock mux state. Further, lc_raw_clk_en_i needs to remain
//    asserted (set to lc_ctrl_pkg::On) for 16 consecutive cycles for triggering the clock switch.
// 3) It is assumed that the clock frequency ratio clk_fast / clk_slow <= 4
//

`include "prim_assert.sv"

module otp_ctrl_clk_mux (
  input                      clk_i,
  input                      rst_ni,
  input                      clk_raw_i,
  input lc_ctrl_pkg::lc_tx_t lc_raw_clk_en_i,
  input                      test_en_i,
  output logic               clk_o
);

  // Encoding generated with ./sparse-fsm-encode.py -d 5 -m 4 -n 8 -s 188565087
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: --
  // 4: --
  // 5: |||||||||||||||||||| (66.67%)
  // 6: |||||||||| (33.33%)
  // 7: --
  // 8: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  //
  localparam int StateWidth = 8;
  typedef enum logic [StateWidth-1:0] {
    StandardSt = 8'b00101100,
    DisableSt  = 8'b01011111,
    WaitSt     = 8'b10000001,
    RawClkSt   = 8'b11110010
  } state_e;

  logic [3:0] cnt_q;
  logic clk_en, cnt_en;
  state_e state_d, state_q;
  logic mux_sel_d, mux_sel_q;

  always_comb begin : p_fsm
    // Default assignments
    state_d = state_q;

    cnt_en     = 1'b1;
    clk_en     = 1'b0;
    mux_sel_d  = 1'b0;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // Default state, where the standard clock is enabled.
      StandardSt: begin
        clk_en     = 1'b1;
        mux_sel_d  = 1'b0;
        // The switch signal must remain asserted for 16 cycles.
        if (lc_raw_clk_en_i == lc_ctrl_pkg::On) begin
          cnt_en = 1'b1;
          if (&cnt_q) begin
            state_d = DisableSt;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First transition state where we disable the clock gate.
      // Wait a couple of cycles to make sure the clock enable signal has
      // disabled the gate.
      DisableSt: begin;
        state_d    = WaitSt;
        clk_en     = 1'b0;
        mux_sel_d  = 1'b0;
        cnt_en     = 1'b1;
        if (&cnt_q) begin
          state_d = RawClkSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Second transition state where we switch the clock mux and
      // wait for 16 cycles such that the clock can stabilize.
      WaitSt: begin;
        clk_en     = 1'b0;
        mux_sel_d  = 1'b1;
        cnt_en     = 1'b1;
        if (&cnt_q) begin
          state_d = RawClkSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // This is the muxed state, where the RAW unlock clock is fed through.
      // Note that this state is terminal.
      RawClkSt: begin
        clk_en     = 1'b1;
        mux_sel_d  = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
      // Note that all parasitic states go back to the StandardSt. Also,
      // they behave the same as the StandardSt in the sense that the standard
      // clock remains enabled.
      default: begin
        state_d   = StandardSt;
        clk_en    = 1'b1;
        mux_sel_d = 1'b0;
      end
      ///////////////////////////////////////////////////////////////////
    endcase
  end


  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(StandardSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d ),
    .q_o ( state_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      mux_sel_q <= 1'b0;
      cnt_q     <= '0;
    end else begin
      mux_sel_q <= mux_sel_d;
      if (cnt_en) begin
        cnt_q <= cnt_q + 1;
      end else begin
        cnt_q <= '0;
      end
    end
  end

  // Clock mux
  logic clk_muxed;
  prim_clock_mux2 i_prim_clock_mux2 (
    .clk0_i (clk_i),
    .clk1_i (clk_raw_i),
    .sel_i  (mux_sel_q & ~test_en_i), // Use clock 0 for testmode.
    .clk_o  (clk_muxed)
  );

  // Synchronize the clock enable to the clk_muxed domain.
  logic clk_en_synced;
  prim_flop_2sync #(
    .Width(1)
  ) i_prim_flop_2sync (
    .clk_i (clk_muxed),
    .rst_ni,
    .d_i   (clk_en),
    .q_o   (clk_en_synced)
  );

  // Feed the clock enable into the clock gate.
  prim_clock_gating prim_clock_gating (
    .clk_i (clk_muxed),
    .en_i  (clk_en_synced),
    .test_en_i,
    .clk_o
  );

endmodule : otp_ctrl_clk_mux
