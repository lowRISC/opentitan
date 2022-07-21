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
        if (!enable_i) begin
          state_d = Idle;
        end else begin
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
