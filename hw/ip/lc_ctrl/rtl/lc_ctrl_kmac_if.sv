// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Synchronization interface between LC FSM and KMAC.
//

`include "prim_assert.sv"

module lc_ctrl_kmac_if
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
(
  // Life cycle controller clock
  input                         clk_i,
  input                         rst_ni,
  // Clock for KMAC interface
  input                         clk_kmac_i,
  input                         rst_kmac_ni,
  // Life cycle hashing interface for raw unlock
  // Synchronized in the life cycle controller.
  input  kmac_pkg::app_rsp_t    kmac_data_i,
  output kmac_pkg::app_req_t    kmac_data_o,
  // Token hashing interface to LC FSM'
  input lc_token_t              transition_token_i,
  input                         token_hash_req_i,
  // Used for gating assertions inside CDC primitives.
  input                         token_hash_req_chk_i,
  output logic                  token_hash_ack_o,
  output logic                  token_hash_err_o,
  output logic                  token_if_fsm_err_o,
  output lc_token_t             hashed_token_o
);

  //////////////////////////////////////
  // Data and Handshake Synchronizers //
  //////////////////////////////////////

  logic kmac_req, kmac_ack;
  lc_token_t kmac_transition_token;
  logic token_hash_req;

  // The transition_token_i register is guaranteed to remain stable once a life cycle
  // transition has been initiated.
  // Hence no further synchronization registers are required on the outgoing data.
  // We just instantiate this synchronizer instance to facilitate CDC tooling (i.e., we
  // make sure the CDC paths go through a prim_sync_reqack_data instance).
  prim_sync_reqack_data #(
    .Width(LcTokenWidth),
    .DataSrc2Dst(1'b1)
  ) u_prim_sync_reqack_data_out (
    .clk_src_i  ( clk_i                 ),
    .rst_src_ni ( rst_ni                ),
    .clk_dst_i  ( clk_kmac_i            ),
    .rst_dst_ni ( rst_kmac_ni           ),
    .req_chk_i  ( token_hash_req_chk_i  ),
    .src_req_i  ( token_hash_req        ),
    .src_ack_o  (                       ), // not connected
    .dst_req_o  (                       ), // not connected
    .dst_ack_i  ( kmac_ack              ),
    .data_i     ( transition_token_i    ),
    .data_o     ( kmac_transition_token )
  );

  // Second synchronizer instance for handshake and return data synchronization.
  logic token_hash_ack_d, token_hash_ack_q;
  logic token_hash_err_q, token_hash_err_d;
  lc_token_t hashed_token_q, hashed_token_d;
  prim_sync_reqack_data #(
    // Token + Error bit
    .Width      (LcTokenWidth + 1),
    .DataSrc2Dst(1'b0),
    // This instantiates a data register
    // on the destination side.
    .DataReg    (1'b1)
  ) u_prim_sync_reqack_data_in (
    .clk_src_i  ( clk_i                ),
    .rst_src_ni ( rst_ni               ),
    .clk_dst_i  ( clk_kmac_i           ),
    .rst_dst_ni ( rst_kmac_ni          ),
    .req_chk_i  ( token_hash_req_chk_i ),
    .src_req_i  ( token_hash_req       ),
    .src_ack_o  ( token_hash_ack_d     ),
    .dst_req_o  ( kmac_req             ),
    .dst_ack_i  ( kmac_ack             ),
    // Truncate hash to 128bit and remove masking (not required here).
    .data_i     ( {kmac_data_i.error,
                   kmac_data_i.digest_share0[LcTokenWidth-1:0] ^
                   kmac_data_i.digest_share1[LcTokenWidth-1:0]} ),
    .data_o     ( {token_hash_err_d,
                   hashed_token_d}     )
  );

  logic unused_sigs;
  assign unused_sigs = ^{
    kmac_data_i.digest_share0[LcTokenWidth +: (kmac_pkg::AppDigestW - LcTokenWidth)],
    kmac_data_i.digest_share1[LcTokenWidth +: (kmac_pkg::AppDigestW - LcTokenWidth)]
  };

  // Hashed Token Register Running on LC Clock
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_lc_regs
    if (!rst_ni) begin
        token_hash_ack_q <= 1'b0;
        token_hash_err_q <= 1'b0;
        hashed_token_q   <= {LcTokenWidth{1'b1}};
    end else begin
      token_hash_ack_q <= token_hash_ack_d;
      // Latch synchronized token and error bit
      if (token_hash_req_i && token_hash_ack_d) begin
        token_hash_err_q <= token_hash_err_d;
        hashed_token_q   <= hashed_token_d;
      end
    end
  end

  assign token_hash_ack_o = token_hash_ack_q;
  assign token_hash_err_o = token_hash_err_q;
  assign hashed_token_o   = hashed_token_q;

  // Stop requesting tokens upon latching on LC side.
  assign token_hash_req = token_hash_req_i & ~token_hash_ack_q;

  /////////////////////////////////////////////
  // Serialization FSM Running on KMAC Clock //
  /////////////////////////////////////////////

  // SEC_CM: KMAC.FSM.SPARSE
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 4 -n 8 \
  //      -s 3343913945 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (66.67%)
  //  6: |||||||||| (33.33%)
  //  7: --
  //  8: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 6
  //
  localparam int StateWidth = 8;
  typedef enum logic [StateWidth-1:0] {
    FirstSt  = 8'b01011011,
    SecondSt = 8'b10010100,
    WaitSt   = 8'b11100111,
    DoneSt   = 8'b00101000
  } state_e;

  state_e state_d, state_q;

  // Serialize the 128bit token into two 64bit beats.
  always_comb begin : p_kmac
    state_d = state_q;
    kmac_data_o = '0;
    kmac_ack = 1'b0;
    token_if_fsm_err_o = 1'b0;

    unique case (state_q)
      // Wait for request and transfer first half of
      // LC token.
      FirstSt: begin
        if (kmac_req) begin
          kmac_data_o.valid = 1'b1;
          kmac_data_o.strb  = 8'hFF;
          kmac_data_o.data  = kmac_transition_token[0 +: 64];
          if (kmac_data_i.ready) begin
            state_d = SecondSt;
          end
        end
      end
      // Transfer second half of LC token.
      SecondSt: begin
        kmac_data_o.valid = 1'b1;
        kmac_data_o.strb  = 8'hFF;
        kmac_data_o.last = 1'b1;
        kmac_data_o.data  = kmac_transition_token[64 +: 64];
        if (kmac_data_i.ready) begin
          state_d = WaitSt;
        end
      end
      // Wait for hashed token response and go to terminal state.
      WaitSt: begin
        if (kmac_data_i.done) begin
          kmac_ack = 1'b1;
          state_d = DoneSt;
        end
      end
      // Terminal state (by design we can only perform
      // one token hashing operation per reset cycle).
      DoneSt: ;
      default: begin
        token_if_fsm_err_o = 1'b1;
      end
    endcase // state_q
  end

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, FirstSt, clk_kmac_i, rst_kmac_ni)

endmodule : lc_ctrl_kmac_if
