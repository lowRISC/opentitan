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
  input keymgr_sideload_clr_e clr_key_i, // clear key just deletes the key
  input wipe_key_i,  // wipe key deletes and renders sideloads useless until reboot
  input [Shares-1:0][RandWidth-1:0] entropy_i,
  input keymgr_key_dest_e dest_sel_i,
  input keymgr_gen_out_e key_sel_i,
  input data_en_i,
  input data_valid_i,
  input hw_key_req_t key_i,
  input [Shares-1:0][kmac_pkg::AppDigestW-1:0] data_i,
  output logic prng_en_o,
  output hw_key_req_t aes_key_o,
  output hw_key_req_t kmac_key_o,
  output otbn_key_req_t otbn_key_o
);

  // Enumeration for working state
  typedef enum logic [2:0] {
    StSideloadReset,
    StSideloadIdle,
    StSideloadWipe,
    StSideloadStop
  } keymgr_sideload_e;

  keymgr_sideload_e state_q, state_d;
  logic keys_en;

  logic [Shares-1:0][KeyWidth-1:0] data_truncated;
  for(genvar i = 0; i < Shares; i++) begin : gen_truncate_data
    assign data_truncated[i] = data_i[i][KeyWidth-1:0];
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StSideloadReset;
    end else begin
      state_q <= state_d;
    end
  end

  // clear all keys when selected by software, or when
  // wipe command is received
  logic clr_all_keys;
  assign clr_all_keys = wipe_key_i |
                        !(clr_key_i inside {SideLoadClrIdle,
                                            SideLoadClrAes,
                                            SideLoadClrKmac,
                                            SideLoadClrOtbn});
  logic aes_clr, kmac_clr, otbn_clr;
  assign aes_clr  = clr_all_keys | (clr_key_i == SideLoadClrAes);
  assign kmac_clr = clr_all_keys | (clr_key_i == SideLoadClrKmac);
  assign otbn_clr = clr_all_keys | (clr_key_i == SideLoadClrOtbn);

  logic clr;
  assign clr = aes_clr | kmac_clr | otbn_clr;

  always_comb begin
    keys_en = 1'b0;
    state_d = state_q;

    unique case (state_q)
      StSideloadReset: begin
        if (init_i) begin
          state_d = StSideloadIdle;
        end
      end

      // when clear is received, delete the selected key
      // when wipe is received, delete the key and disable sideload until reboot.
      StSideloadIdle: begin
        keys_en = 1'b1;
        if (wipe_key_i) begin
          state_d = StSideloadWipe;
        end
      end

      StSideloadWipe: begin
        keys_en = 1'b0;
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

  logic aes_sel, kmac_sel, otbn_sel;
  assign aes_sel  = dest_sel_i == Aes  & key_sel_i == HwKey;
  assign kmac_sel = dest_sel_i == Kmac & key_sel_i == HwKey;
  assign otbn_sel = dest_sel_i == Otbn & key_sel_i == HwKey;

  keymgr_sideload_key u_aes_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_en_i(data_en_i),
    .set_i(data_valid_i & aes_sel),
    .clr_i(aes_clr),
    .entropy_i(entropy_i),
    .key_i(data_truncated),
    .valid_o(aes_key_o.valid),
    .key_o(aes_key_o.key)
  );

  keymgr_sideload_key #(
    .Width(OtbnKeyWidth)
  ) u_otbn_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_en_i(data_en_i),
    .set_i(data_valid_i & otbn_sel),
    .clr_i(otbn_clr),
    .entropy_i(entropy_i),
    .key_i(data_i),
    .valid_o(otbn_key_o.valid),
    .key_o(otbn_key_o.key)
  );

  hw_key_req_t kmac_sideload_key;
  keymgr_sideload_key u_kmac_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_en_i(data_en_i),
    .set_i(data_valid_i & kmac_sel),
    .clr_i(kmac_clr),
    .entropy_i(entropy_i),
    .key_i(data_truncated),
    .valid_o(kmac_sideload_key.valid),
    .key_o(kmac_sideload_key.key)
  );

  // when directed by keymgr_ctrl, switch over to internal key and feed to kmac
  assign kmac_key_o = key_i.valid ? key_i : kmac_sideload_key;

  // when clearing, request prng
  assign prng_en_o = clr;


  /////////////////////////////////////
  //  Assertions
  /////////////////////////////////////

  // When updating a sideload key, the secret key state must always be used as the source
  `ASSERT(KmacKeySource_a, data_valid_i |-> key_i.valid)

endmodule // keymgr_sideload_key_ctrl
