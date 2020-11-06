// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng instantiation request state machine module
//
//   handles instantiation requests from all requesting interfaces

module csrng_main_sm import csrng_pkg::*; (
  input logic                clk_i,
  input logic                rst_ni,

   // ins req interface
  input logic                acmd_avail_i,
  output logic               acmd_accept_o,
  input logic [2:0]          acmd_i,
  input logic                acmd_eop_i,
  input logic                ctr_drbg_cmd_req_rdy_i,
  input logic                flag0_i,
  output logic               cmd_entropy_req_o,
  input logic                cmd_entropy_avail_i,
  output logic               instant_req_o,
  output logic               reseed_req_o,
  output logic               generate_req_o,
  output logic               update_req_o,
  output logic               uninstant_req_o
);

  // Encoding generated with ./sparse-fsm-encode.py -d 3 -m 9 -n 8 -s 3053040243
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: |||||||||||||||||||| (30.56%)
  // 4: |||||||||||||||||||| (30.56%)
  // 5: |||||||||||| (19.44%)
  // 6: ||||||||| (13.89%)
  // 7: ||| (5.56%)
  // 8: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 7
  //

  localparam int StateWidth = 8;
  typedef    enum logic [StateWidth-1:0] {
    Idle    =      8'b01100100, // idle
    InstantPrep  = 8'b11000010, // instantiate prep
    InstantReq   = 8'b11000101, // instantiate request (takes adata or entropy)
    ReseedPrep   = 8'b00010001, // reseed prep
    ReseedReq    = 8'b10110010, // reseed request (takes adata and entropy and Key,V,RC)
    GenerateReq  = 8'b01111010, // generate request (takes adata? and Key,V,RC)
    UpdatePrep   = 8'b00001101, // update prep
    UpdateReq    = 8'b10101011, // update request (takes adata and Key,V,RC)
    UninstantReq = 8'b00101000  // uninstantiate request (no input)
  } state_e;

  state_e state_d, state_q;

  logic [StateWidth-1:0] state_raw_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(Idle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d ),
    .q_o ( state_raw_q )
  );

  assign state_q = state_e'(state_raw_q);

  always_comb begin
    state_d = state_q;
    acmd_accept_o = 1'b0;
    cmd_entropy_req_o = 1'b0;
    instant_req_o = 1'b0;
    reseed_req_o = 1'b0;
    generate_req_o = 1'b0;
    update_req_o = 1'b0;
    uninstant_req_o = 1'b0;
    unique case (state_q)
      Idle: begin
        if (ctr_drbg_cmd_req_rdy_i) begin
          if (acmd_avail_i) begin
            acmd_accept_o = 1'b1;
            if (acmd_i == INS) begin
              if (acmd_eop_i) begin
                state_d = InstantPrep;
              end
            end else if (acmd_i == RES) begin
              if (acmd_eop_i) begin
                state_d = ReseedPrep;
              end
            end else if (acmd_i == GEN) begin
              state_d = GenerateReq;
            end else if (acmd_i == UPD) begin
              if (acmd_eop_i) begin
                state_d = UpdatePrep;
              end
            end else if (acmd_i == UNI) begin
              state_d = UninstantReq;
            end
          end
        end
      end
      InstantPrep: begin
        if (flag0_i) begin
          // assumes all adata is present now
          state_d = InstantReq;
        end else begin
          // delay one clock to fix timing issue
          cmd_entropy_req_o = 1'b1;
          if (cmd_entropy_avail_i) begin
            state_d = InstantReq;
          end
        end
      end
      InstantReq: begin
        instant_req_o = 1'b1;
        state_d = Idle;
      end
      ReseedPrep: begin
        acmd_accept_o = 1'b1;
        cmd_entropy_req_o = 1'b1;
        // assumes all adata is present now
        if (cmd_entropy_avail_i) begin
          state_d = ReseedReq;
        end
      end
      ReseedReq: begin
        reseed_req_o = 1'b1;
        state_d = Idle;
      end
      GenerateReq: begin
        acmd_accept_o = 1'b1;
        generate_req_o = 1'b1;
        state_d = Idle;
      end
      UpdatePrep: begin
        // assumes all adata is present now
        acmd_accept_o = 1'b1;
        state_d = UpdateReq;
      end
      UpdateReq: begin
        update_req_o = 1'b1;
        state_d = Idle;
      end
      UninstantReq: begin
        uninstant_req_o = 1'b1;
        state_d = Idle;
      end
      default: state_d = Idle;
    endcase
  end

endmodule
