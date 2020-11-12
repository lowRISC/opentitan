// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Manage all sideload keys

`include "prim_assert.sv"

module keymgr_sideload_key_ctrl import keymgr_pkg::*;(
  input clk_i,
  input rst_ni,
  input en_i,
  input init_i,
  input [31:0] entropy_i,
  input keymgr_key_dest_e dest_sel_i,
  input keymgr_gen_out_e key_sel_i,
  input load_key_i,
  input data_valid_i,
  input [Shares-1:0][KeyWidth-1:0] key_i,
  input [Shares-1:0][KeyWidth-1:0] data_i,
  output logic prng_en_o,
  output hw_key_req_t aes_key_o,
  output hw_key_req_t hmac_key_o,
  output hw_key_req_t kmac_key_o
);

  // Enumeration for working state
  typedef enum logic [1:0] {
    StReset,
    StIdle,
    StWipe,
    StStop
  } keymgr_sideload_e;

  keymgr_sideload_e state_q, state_d;
  logic [3:0] cnt_q, cnt_d;
  logic cnt_end;
  logic clr;
  logic keys_en;


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StReset;
      cnt_q <= '0;
    end else begin
      state_q <= state_d;
      cnt_q <= cnt_d;
    end
  end

  assign cnt_end = cnt_q[3];
  assign cnt_d = cnt_end ? cnt_q :
                 clr     ? cnt_q + 1'b1 : cnt_q;

  always_comb begin

    clr = 1'b0;
    keys_en = 1'b0;
    state_d = state_q;

    unique case (state_q)
      StReset: begin
        if (init_i && en_i) begin
          state_d = StIdle;
        end
      end

      StIdle: begin
        keys_en = 1'b1;
        if (!en_i) begin
          keys_en = 1'b0;
          state_d = StWipe;
        end
      end

      StWipe: begin
        keys_en = 1'b0;
        clr = 1'b1;
        state_d = StStop;
      end

      // intentional terminal state
      StStop: begin
        keys_en = 1'b0;
      end

      default:;
    endcase // unique case (state_q)
  end

  logic aes_sel, hmac_sel, kmac_sel;
  assign aes_sel  = dest_sel_i == Aes  & key_sel_i == HwKey;
  assign hmac_sel = dest_sel_i == Hmac & key_sel_i == HwKey;
  assign kmac_sel = dest_sel_i == Kmac & key_sel_i == HwKey;

  keymgr_sideload_key u_aes_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_i(data_valid_i & aes_sel),
    .clr_i(clr), // TBD, should add an option for software clear later
    .entropy_i(entropy_i),
    .key_i(data_i),
    .key_o(aes_key_o)
  );

  keymgr_sideload_key u_hmac_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_i(data_valid_i & hmac_sel),
    .clr_i(clr), // TBD, should add an option for software clear later
    .entropy_i(entropy_i),
    .key_i(data_i),
    .key_o(hmac_key_o)
  );

  keymgr_sideload_key u_kmac_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_i(load_key_i | (data_valid_i & kmac_sel)),
    .clr_i(clr), // TBD, should add an option for software clear laterclr
    .entropy_i(entropy_i),
    .key_i(load_key_i ? key_i : data_i),
    .key_o(kmac_key_o)
  );

  // when clearing, request prng
  assign prng_en_o = clr;


  /////////////////////////////////////
  //  Assertions
  /////////////////////////////////////

  // Only 1 entity should be trying to use the secret kmac key input
  `ASSERT(KmacKeyLoadExclusive_a, $onehot0({load_key_i, data_valid_i & kmac_sel}))

endmodule // keymgr_sideload_key_ctrl
