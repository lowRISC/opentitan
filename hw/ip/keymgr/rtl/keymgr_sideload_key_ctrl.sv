// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Manage all sideload keys

`include "prim_assert.sv"

module keymgr_sideload_key_ctrl import keymgr_pkg::*;(
  input clk_i,
  input rst_ni,
  input init_i,
  input clr_key_i,   // clear key just deletes the key
  input wipe_key_i,  // wipe key deletes and renders sideloads useless until reboot
  input [Shares-1:0][RandWidth-1:0] entropy_i,
  input keymgr_key_dest_e dest_sel_i,
  input keymgr_gen_out_e key_sel_i,
  input load_key_i,
  input data_en_i,
  input data_valid_i,
  input hw_key_req_t key_i,
  input [Shares-1:0][KeyWidth-1:0] data_i,
  output logic prng_en_o,
  output hw_key_req_t aes_key_o,
  output hw_key_req_t hmac_key_o,
  output hw_key_req_t kmac_key_o
);

  // Enumeration for working state
  typedef enum logic [2:0] {
    StSideloadReset,
    StSideloadIdle,
    StSideloadClear,
    StSideloadWipe,
    StSideloadStop
  } keymgr_sideload_e;

  keymgr_sideload_e state_q, state_d;
  logic [3:0] cnt_q, cnt_d;
  logic cnt_end;
  logic clr;
  logic keys_en;


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StSideloadReset;
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
      StSideloadReset: begin
        if (init_i) begin
          state_d = StSideloadIdle;
        end
      end

      // when clear is received, delete the key and return to idle.
      // when wipe is received, delete the key and disable sideload until reboot.
      StSideloadIdle: begin
        keys_en = 1'b1;
        if (wipe_key_i || clr_key_i) begin
          state_d = wipe_key_i ? StSideloadWipe : StSideloadClear;
        end
      end

      // if wipe asserts while clearing, follow the normal wipe protocol
      StSideloadClear: begin
        keys_en = 1'b0;
        clr = 1'b1;
        if (wipe_key_i) begin
          state_d = StSideloadWipe;
        end else if (!clr_key_i) begin
          state_d = StSideloadIdle;
        end
      end

      StSideloadWipe: begin
        keys_en = 1'b0;
        clr = 1'b1;
        if (!wipe_key_i) begin
          state_d = StSideloadStop;
        end
      end

      // intentional terminal state
      StSideloadStop: begin
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
    .set_en_i(data_en_i),
    .set_i(data_valid_i & aes_sel),
    .clr_i(clr),
    .entropy_i(entropy_i),
    .key_i(data_i),
    .key_o(aes_key_o)
  );

  keymgr_sideload_key u_hmac_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_en_i(data_en_i),
    .set_i(data_valid_i & hmac_sel),
    .clr_i(clr),
    .entropy_i(entropy_i),
    .key_i(data_i),
    .key_o(hmac_key_o)
  );

  hw_key_req_t kmac_sideload_key;
  keymgr_sideload_key u_kmac_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_en_i(data_en_i),
    .set_i(data_valid_i & kmac_sel),
    .clr_i(clr),
    .entropy_i(entropy_i),
    .key_i(data_i),
    .key_o(kmac_sideload_key)
  );

  // when directed by keymgr_ctrl, switch over to internal key and feed to kmac
  assign kmac_key_o = load_key_i ? key_i : kmac_sideload_key;

  // when clearing, request prng
  assign prng_en_o = clr;


  /////////////////////////////////////
  //  Assertions
  /////////////////////////////////////

  // When updating a sideload key, the secret key state must always be used as the source
  `ASSERT(KmacKeySource_a, data_valid_i |-> load_key_i)

endmodule // keymgr_sideload_key_ctrl
