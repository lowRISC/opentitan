// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng app cmd request state machine module
//
//  - handles all app cmd requests from all requesting interfaces

module csrng_main_sm import csrng_pkg::*; #(
  parameter int StateWidth = 8
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
  output logic                  main_sm_alert_o,
  output logic                  main_sm_err_o
);

  state_e state_d, state_q;
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, Idle)

  assign main_sm_state_o = {state_q};

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
    main_sm_alert_o = 1'b0;
    main_sm_err_o = 1'b0;

    if (state_q == Error) begin
      // In case we are in the Error state we must ignore the local escalate and enable signals.
      main_sm_err_o = 1'b1;
    end else if (local_escalate_i) begin
      // In case local escalate is high we must transition to the error state.
      state_d = Error;
    end else if (!enable_i && state_q inside {Idle, ParseCmd, InstantPrep, InstantReq, ReseedPrep,
                                              ReseedReq, GeneratePrep, GenerateReq, UpdatePrep,
                                              UpdateReq, UninstantPrep, UninstantReq, ClrAData,
                                              CmdCompWait}) begin
      // In case the module is disabled and we are in a legal state we must go into idle state.
      state_d = Idle;
    end else begin
      // Otherwise do the state machine as normal.
      unique case (state_q)
        Idle: begin
          // Because of the if statement above we won't leave idle if enable is low.
          if (ctr_drbg_cmd_req_rdy_i) begin
            // Signal the arbiter to grant this request.
            if (acmd_avail_i) begin
              acmd_accept_o = 1'b1;
              state_d = ParseCmd;
            end
          end
        end
        ParseCmd: begin
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
            end else begin
              // command was not supported
              main_sm_alert_o = 1'b1;
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
          state_d = ClrAData;
        end
        ReseedPrep: begin
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
        ReseedReq: begin
          reseed_req_o = 1'b1;
          state_d = ClrAData;
        end
        GeneratePrep: begin
          // assumes all adata is present now
          state_d = GenerateReq;
        end
        GenerateReq: begin
          generate_req_o = 1'b1;
          state_d = ClrAData;
        end
        UpdatePrep: begin
          // assumes all adata is present now
          state_d = UpdateReq;
        end
        UpdateReq: begin
          update_req_o = 1'b1;
          state_d = ClrAData;
        end
        UninstantPrep: begin
          // assumes all adata is present now
          state_d = UninstantReq;
        end
        UninstantReq: begin
          uninstant_req_o = 1'b1;
          state_d = ClrAData;
        end
        ClrAData: begin
          clr_adata_packer_o = 1'b1;
          state_d = CmdCompWait;
        end
        CmdCompWait: begin
          if (cmd_complete_i) begin
            state_d = Idle;
          end
        end
        // Error: The error state is now covered by the if statement above.
        default: begin
          state_d = Error;
          main_sm_err_o = 1'b1;
        end
      endcase
    end
  end

endmodule
