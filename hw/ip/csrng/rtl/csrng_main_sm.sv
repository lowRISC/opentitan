// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng app cmd request state machine module
//
//  - handles all app cmd requests from all requesting interfaces

`include "prim_assert.sv"

module csrng_main_sm import csrng_pkg::*; (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  input  logic                        enable_i,

  input  logic                        acmd_avail_i,
  output logic                        acmd_accept_o,
  input  acmd_e                       acmd_i,
  input  logic                        acmd_eop_i,

  input  logic                        flag0_i,

  output logic                        cmd_entropy_req_o,
  input  logic                        cmd_entropy_avail_i,

  output logic                        cmd_vld_o,
  input  logic                        cmd_rdy_i,
  output logic                        clr_adata_packer_o,
  input  logic                        cmd_complete_i,

  input  logic                        local_escalate_i,

  output logic [MainSmStateWidth-1:0] main_sm_state_o,
  output logic                        main_sm_err_o
);

  // SEC_CM: MAIN_SM.FSM.SPARSE
  main_sm_state_e state_d, state_q;
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, main_sm_state_e, MainSmIdle)

  assign main_sm_state_o = {state_q};

  always_comb begin
    state_d            = state_q;
    acmd_accept_o      = 1'b0;
    cmd_entropy_req_o  = 1'b0;
    cmd_vld_o          = 1'b0;
    clr_adata_packer_o = 1'b0;
    main_sm_err_o      = 1'b0;

    if (state_q == MainSmError) begin
      // In case we are in the Error state we must ignore the local escalate and enable signals.
      main_sm_err_o = 1'b1;
    end else if (local_escalate_i) begin
      // In case local escalate is high we must transition to the error state.
      state_d = MainSmError;
    end else if (!enable_i && state_q inside {MainSmIdle, MainSmParseCmd, MainSmEntropyReq,
                                              MainSmCmdPrep, MainSmCmdVld,
                                              MainSmClrAData, MainSmCmdCompWait}) begin
      // In case the module is disabled and we are in a legal state we must go into idle state.
      state_d = MainSmIdle;
    end else begin
      // Otherwise do the state machine as normal.
      unique case (state_q)
        MainSmIdle: begin
          // Signal the arbiter to grant this request.
          if (acmd_avail_i) begin
            acmd_accept_o = 1'b1;
            state_d = MainSmParseCmd;
          end
        end
        MainSmParseCmd: begin
          if (acmd_eop_i) begin
            unique case (acmd_i)
              INS, RES:      state_d = MainSmEntropyReq; // Command may require entropy
              GEN, UPD, UNI: state_d = MainSmCmdPrep;    // Command does not require entropy
              default:       state_d = MainSmIdle;       // Command was not supported
            endcase
          end
        end
        MainSmEntropyReq: begin
          if (flag0_i) begin
            // With flag0 set, no entropy is required.
            state_d = MainSmCmdVld;
          end else begin
            // Delay one clock to fix timing issue.
            cmd_entropy_req_o = 1'b1;
            if (cmd_entropy_avail_i) begin
              state_d = MainSmCmdVld;
            end
          end
        end
        MainSmCmdPrep: begin
          // Assumes all adata is present now.
          state_d = MainSmCmdVld;
        end
        MainSmCmdVld: begin
          cmd_vld_o = 1'b1;
          if (cmd_rdy_i) begin
            if (cmd_complete_i) begin
              clr_adata_packer_o = 1'b1;
              state_d = MainSmIdle;
            end else begin
              state_d = MainSmClrAData;
            end
          end
        end
        MainSmClrAData: begin
          clr_adata_packer_o = 1'b1;
          if (cmd_complete_i) begin
            state_d = MainSmIdle;
          end else begin
            state_d = MainSmCmdCompWait;
          end
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
