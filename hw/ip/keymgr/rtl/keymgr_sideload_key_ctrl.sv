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
  input prim_mubi_pkg::mubi4_t hw_key_sel_i,
  input data_en_i,
  input data_valid_i,
  input hw_key_req_t key_i,
  input [Shares-1:0][kmac_pkg::AppDigestW-1:0] data_i,
  output logic prng_en_o,
  output hw_key_req_t aes_key_o,
  output hw_key_req_t kmac_key_o,
  output otbn_key_req_t otbn_key_o,
  output logic sideload_sel_err_o,
  output logic fsm_err_o
);

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 4 -n 10 \
  //      -s 1700801647 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (33.33%)
  //  6: |||||||||| (16.67%)
  //  7: |||||||||||||||||||| (33.33%)
  //  8: |||||||||| (16.67%)
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
    StSideloadReset = 10'b0011111011,
    StSideloadIdle  = 10'b0101000101,
    StSideloadWipe  = 10'b1110110010,
    StSideloadStop  = 10'b1000001010
  } keymgr_sideload_e;

  keymgr_sideload_e state_q, state_d;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, keymgr_sideload_e, StSideloadReset)

  logic keys_en;
  logic [Shares-1:0][KeyWidth-1:0] data_truncated;
  for(genvar i = 0; i < Shares; i++) begin : gen_truncate_data
    assign data_truncated[i] = data_i[i][KeyWidth-1:0];
  end

  // clear all keys when selected by software, or when
  // wipe command is received
  logic clr_all_keys;
  logic [LastIdx-1:0] slot_clr;
  assign clr_all_keys = wipe_key_i |
                        !(clr_key_i inside {SideLoadClrIdle,
                                            SideLoadClrAes,
                                            SideLoadClrKmac,
                                            SideLoadClrOtbn});

  assign slot_clr[AesIdx]  = clr_all_keys | (clr_key_i == SideLoadClrAes);
  assign slot_clr[KmacIdx] = clr_all_keys | (clr_key_i == SideLoadClrKmac);
  assign slot_clr[OtbnIdx] = clr_all_keys | (clr_key_i == SideLoadClrOtbn);

  logic clr;
  assign clr = |slot_clr;

  always_comb begin
    keys_en = 1'b0;
    state_d = state_q;
    fsm_err_o = 1'b0;

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

      default: begin
        fsm_err_o = 1'b1;
      end

    endcase // unique case (state_q)
  end

  import prim_mubi_pkg::mubi4_test_true_strict;
  prim_mubi_pkg::mubi4_t [LastIdx-1:0] hw_key_sel;
  prim_mubi4_sync #(
    .NumCopies(int'(LastIdx)),
    .AsyncOn(0) // clock/reset below is only used for SVAs.
  ) u_mubi_buf (
    .clk_i,
    .rst_ni,
    .mubi_i(hw_key_sel_i),
    .mubi_o(hw_key_sel)
  );

  logic [LastIdx-1:0] slot_sel;
  assign slot_sel[AesIdx] = (dest_sel_i == Aes) & mubi4_test_true_strict(hw_key_sel[AesIdx]);
  assign slot_sel[KmacIdx] = (dest_sel_i == Kmac) & mubi4_test_true_strict(hw_key_sel[KmacIdx]);
  assign slot_sel[OtbnIdx] = (dest_sel_i == Otbn) & mubi4_test_true_strict(hw_key_sel[OtbnIdx]);

  keymgr_sideload_key u_aes_key (
    .clk_i,
    .rst_ni,
    .en_i(keys_en),
    .set_en_i(data_en_i),
    .set_i(data_valid_i & slot_sel[AesIdx]),
    .clr_i(slot_clr[AesIdx]),
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
    .set_i(data_valid_i & slot_sel[OtbnIdx]),
    .clr_i(slot_clr[OtbnIdx]),
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
    .set_i(data_valid_i & slot_sel[KmacIdx]),
    .clr_i(slot_clr[KmacIdx]),
    .entropy_i(entropy_i),
    .key_i(data_truncated),
    .valid_o(kmac_sideload_key.valid),
    .key_o(kmac_sideload_key.key)
  );

  logic [LastIdx-1:0] valid_tracking_q;
  for (genvar i = int'(AesIdx); i < LastIdx; i++) begin : gen_tracking_valid
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        valid_tracking_q[i] <= '0;
      end else if (slot_clr[i]) begin
        valid_tracking_q[i] <= '0;
      end else if (slot_sel[i])begin
        valid_tracking_q[i] <= 1'b1;
      end
    end
  end

  // SEC_CM: SIDE_LOAD_SEL.CTRL.CONSISTENCY
  logic [LastIdx-1:0] valids;
  assign valids[AesIdx] = aes_key_o.valid;
  assign valids[KmacIdx] = kmac_sideload_key.valid;
  assign valids[OtbnIdx] = otbn_key_o.valid;

  // If valid tracking claims a valid should be 0 but 1 is observed, it is
  // an error.
  // Note the sideload error is not a direct constant comparision. Instead
  // it provides hint when valids is allowed to be valid.  If valid becomes
  // 1 outside that window, then an error is triggered.
  assign sideload_sel_err_o = |(~valid_tracking_q & valids);

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
