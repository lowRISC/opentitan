// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng app cmd request state machine module
//
//  - handles all app cmd requests from all requesting interfaces

module csrng_main_sm import csrng_pkg::*; #() (
  input logic                         clk_i,
  input logic                         rst_ni,

  input logic                         enable_i,
  input logic                         acmd_avail_i,
  output logic                        acmd_accept_o,
  input logic [2:0]                   acmd_i,
  input logic                         acmd_eop_i,
  input logic                         ctr_drbg_cmd_req_rdy_i,
  input logic                         flag0_i,
  output logic                        cmd_entropy_req_o,
  input logic                         cmd_entropy_avail_i,
  output logic                        instant_req_o,
  output logic                        reseed_req_o,
  output logic                        generate_req_o,
  output logic                        update_req_o,
  output logic                        uninstant_req_o,
  output logic                        clr_adata_packer_o,
  input logic                         cmd_complete_i,
  input logic                         local_escalate_i,
  output logic [MainSmStateWidth-1:0] main_sm_state_o,
  output logic                        main_sm_alert_o,
  output logic                        main_sm_err_o
);

  main_sm_state_e state_d, state_q;
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, main_sm_state_e, MainSmIdle)

  assign main_sm_state_o = {state_q};

  always_comb begin
    state_d            = state_q;
    acmd_accept_o      = 1'b0;
    cmd_entropy_req_o  = 1'b0;
    instant_req_o      = 1'b0;
    reseed_req_o       = 1'b0;
    generate_req_o     = 1'b0;
    update_req_o       = 1'b0;
    uninstant_req_o    = 1'b0;
    clr_adata_packer_o = 1'b0;
    main_sm_alert_o    = 1'b0;
    main_sm_err_o      = 1'b0;

    if (state_q == MainSmError) begin
      // In case we are in the Error state we must ignore the local escalate and enable signals.
      main_sm_err_o = 1'b1;
    end else if (local_escalate_i) begin
      // In case local escalate is high we must transition to the error state.
      state_d = MainSmError;
    end else if (!enable_i && state_q inside {MainSmIdle, MainSmParseCmd, MainSmInstantPrep,
                                              MainSmInstantReq, MainSmReseedPrep, MainSmReseedReq,
                                              MainSmGeneratePrep, MainSmGenerateReq,
                                              MainSmUpdatePrep, MainSmUpdateReq,
                                              MainSmUninstantPrep, MainSmUninstantReq,
                                              MainSmClrAData, MainSmCmdCompWait}) begin
      // In case the module is disabled and we are in a legal state we must go into idle state.
      state_d = MainSmIdle;
    end else begin
      // Otherwise do the state machine as normal.
      unique case (state_q)
        MainSmIdle: begin
          // Because of the if statement above we won't leave idle if enable is low.
          if (ctr_drbg_cmd_req_rdy_i) begin
            // Signal the arbiter to grant this request.
            if (acmd_avail_i) begin
              acmd_accept_o = 1'b1;
              state_d = MainSmParseCmd;
            end
          end
        end
        MainSmParseCmd: begin
          if (ctr_drbg_cmd_req_rdy_i) begin
            if (acmd_i == INS) begin
              if (acmd_eop_i) begin
                state_d = MainSmInstantPrep;
              end
            end else if (acmd_i == RES) begin
              if (acmd_eop_i) begin
                state_d = MainSmReseedPrep;
              end
            end else if (acmd_i == GEN) begin
              if (acmd_eop_i) begin
                state_d = MainSmGeneratePrep;
              end
            end else if (acmd_i == UPD) begin
              if (acmd_eop_i) begin
                state_d = MainSmUpdatePrep;
              end
            end else if (acmd_i == UNI) begin
              if (acmd_eop_i) begin
                state_d = MainSmUninstantPrep;
              end
            end else begin
              // Command was not supported.
              main_sm_alert_o = 1'b1;
            end
          end
        end
        MainSmInstantPrep: begin
          if (flag0_i) begin
            // Assumes all adata is present now.
            state_d = MainSmInstantReq;
          end else begin
            // Delay one clock to fix timing issue.
            cmd_entropy_req_o = 1'b1;
            if (cmd_entropy_avail_i) begin
              state_d = MainSmInstantReq;
            end
          end
        end
        MainSmInstantReq: begin
          instant_req_o = 1'b1;
          state_d = MainSmClrAData;
        end
        MainSmReseedPrep: begin
          if (flag0_i) begin
            // Assumes all adata is present now.
            state_d = MainSmReseedReq;
          end else begin
            // Delay one clock to fix timing issue.
            cmd_entropy_req_o = 1'b1;
            if (cmd_entropy_avail_i) begin
              state_d = MainSmReseedReq;
            end
          end
        end
        MainSmReseedReq: begin
          reseed_req_o = 1'b1;
          state_d = MainSmClrAData;
        end
        MainSmGeneratePrep: begin
          // Assumes all adata is present now.
          state_d = MainSmGenerateReq;
        end
        MainSmGenerateReq: begin
          generate_req_o = 1'b1;
          state_d = MainSmClrAData;
        end
        MainSmUpdatePrep: begin
          // Assumes all adata is present now.
          state_d = MainSmUpdateReq;
        end
        MainSmUpdateReq: begin
          update_req_o = 1'b1;
          state_d = MainSmClrAData;
        end
        MainSmUninstantPrep: begin
          // Assumes all adata is present now.
          state_d = MainSmUninstantReq;
        end
        MainSmUninstantReq: begin
          uninstant_req_o = 1'b1;
          state_d = MainSmClrAData;
        end
        MainSmClrAData: begin
          clr_adata_packer_o = 1'b1;
          state_d = MainSmCmdCompWait;
        end
        MainSmCmdCompWait: begin
          if (cmd_complete_i) begin
            state_d = MainSmIdle;
          end
        end
        // Error: The error state is now covered by the if statement above.
        default: begin
          state_d = MainSmError;
          main_sm_err_o = 1'b1;
        end
      endcase
    end
  end

  // Make sure that the state machine has a stable error state. This means that after the error
  // state is entered it will not exit it unless a reset signal is received.
  `ASSERT(CsrngMainErrorStStable_A, state_q == MainSmError |=> $stable(state_q))
  // If in error state, the error output must be high.
  `ASSERT(CsrngMainErrorOutput_A,   state_q == MainSmError |-> main_sm_err_o)
endmodule
