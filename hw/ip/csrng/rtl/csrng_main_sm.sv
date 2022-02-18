// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng app cmd request state machine module
//
//  - handles all app cmd requests from all requesting interfaces

module csrng_main_sm import csrng_pkg::*; #(
  localparam int StateWidth = 8
) (
  input logic                   clk_i,
  input logic                   rst_ni,

  input logic                   enable_i,
  input logic                   acmd_avail_i,
  output logic                  acmd_accept_o,
  input logic [2:0]             acmd_i,
  input logic                   acmd_eop_i,
  input logic                   ctr_drbg_cmd_req_rdy_i,
  input logic                   flag0_i,
  output logic                  cmd_entropy_req_o,
  input logic                   cmd_entropy_avail_i,
  output logic                  instant_req_o,
  output logic                  reseed_req_o,
  output logic                  generate_req_o,
  output logic                  update_req_o,
  output logic                  uninstant_req_o,
  output logic                  clr_adata_packer_o,
  input logic                   cmd_complete_i,
  input logic                   local_escalate_i,
  output logic [StateWidth-1:0] main_sm_state_o,
  output logic                  main_sm_err_o
);
// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 15 -n 8 \
//      -s 1300573258 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||| (32.38%)
//  4: |||||||||||||||||||| (35.24%)
//  5: |||||||| (15.24%)
//  6: |||||| (11.43%)
//  7: ||| (5.71%)
//  8: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 7
// Minimum Hamming weight: 1
// Maximum Hamming weight: 7
//

  typedef    enum logic [StateWidth-1:0] {
    Idle          = 8'b01001110, // idle
    ParseCmd      = 8'b10111011, // parse the cmd
    InstantPrep   = 8'b11000001, // instantiate prep
    InstantReq    = 8'b01010100, // instantiate request (takes adata or entropy)
    ReseedPrep    = 8'b11011101, // reseed prep
    ReseedReq     = 8'b01011011, // reseed request (takes adata and entropy and Key,V,RC)
    GeneratePrep  = 8'b11101111, // generate request (takes adata? and Key,V,RC)
    GenerateReq   = 8'b00100100, // generate request (takes adata? and Key,V,RC)
    UpdatePrep    = 8'b00110001, // update prep
    UpdateReq     = 8'b10010000, // update request (takes adata and Key,V,RC)
    UninstantPrep = 8'b11110110, // uninstantiate prep
    UninstantReq  = 8'b01100011, // uninstantiate request
    ClrAData      = 8'b00000010, // clear out the additional data packer fifo
    CmdCompWait   = 8'b10111100, // wait for command to complete
    Error         = 8'b01111000  // error state, results in fatal alert
  } state_e;

  state_e state_d, state_q;

  logic [StateWidth-1:0] state_raw_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.

  prim_sparse_fsm_flop #(
    .StateEnumT(state_e),
    .Width(StateWidth),
    .ResetValue(StateWidth'(Idle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( state_d ),
    .state_o ( state_raw_q )
  );

  assign state_q = state_e'(state_raw_q);
  assign main_sm_state_o = state_raw_q;

  always_comb begin
    state_d = state_q;
    acmd_accept_o = 1'b0;
    cmd_entropy_req_o = 1'b0;
    instant_req_o = 1'b0;
    reseed_req_o = 1'b0;
    generate_req_o = 1'b0;
    update_req_o = 1'b0;
    uninstant_req_o = 1'b0;
    clr_adata_packer_o = 1'b0;
    main_sm_err_o = 1'b0;
    unique case (state_q)
      Idle: begin
        if (enable_i) begin
          if (ctr_drbg_cmd_req_rdy_i) begin
            // signal the arbiter to grant this request
            if (acmd_avail_i) begin
              acmd_accept_o = 1'b1;
              state_d = ParseCmd;
            end
          end
        end
      end
      ParseCmd: begin
        if (enable_i) begin
          if (ctr_drbg_cmd_req_rdy_i) begin
            if (acmd_i == INS) begin
              if (acmd_eop_i) begin
                state_d = InstantPrep;
              end
            end else if (acmd_i == RES) begin
              if (acmd_eop_i) begin
                state_d = ReseedPrep;
              end
            end else if (acmd_i == GEN) begin
              if (acmd_eop_i) begin
                state_d = GeneratePrep;
              end
            end else if (acmd_i == UPD) begin
              if (acmd_eop_i) begin
                state_d = UpdatePrep;
              end
            end else if (acmd_i == UNI) begin
              if (acmd_eop_i) begin
                state_d = UninstantPrep;
              end
            end
          end
        end
      end
      InstantPrep: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
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
      end
      InstantReq: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          instant_req_o = 1'b1;
          state_d = ClrAData;
        end
      end
      ReseedPrep: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (flag0_i) begin
            // assumes all adata is present now
            state_d = ReseedReq;
          end else begin
            // delay one clock to fix timing issue
            cmd_entropy_req_o = 1'b1;
            if (cmd_entropy_avail_i) begin
              state_d = ReseedReq;
            end
          end
        end
      end
      ReseedReq: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          reseed_req_o = 1'b1;
          state_d = ClrAData;
        end
      end
      GeneratePrep: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          // assumes all adata is present now
          state_d = GenerateReq;
        end
      end
      GenerateReq: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          generate_req_o = 1'b1;
          state_d = ClrAData;
        end
      end
      UpdatePrep: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          // assumes all adata is present now
          state_d = UpdateReq;
        end
      end
      UpdateReq: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          update_req_o = 1'b1;
          state_d = ClrAData;
        end
      end
      UninstantPrep: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          // assumes all adata is present now
          state_d = UninstantReq;
        end
      end
      UninstantReq: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          uninstant_req_o = 1'b1;
          state_d = ClrAData;
        end
      end
      ClrAData: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          clr_adata_packer_o = 1'b1;
          state_d = CmdCompWait;
        end
      end
      CmdCompWait: begin
        if (!enable_i) begin
          state_d = Idle;
        end else begin
          if (cmd_complete_i) begin
            state_d = Idle;
          end
        end
      end
      Error: begin
        main_sm_err_o = 1'b1;
      end
      default: state_d = Error;
    endcase
    if (local_escalate_i) begin
      state_d = Error;
    end
  end

endmodule
