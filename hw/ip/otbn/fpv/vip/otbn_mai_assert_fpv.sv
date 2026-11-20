// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for otbn_mai.
// Intended to be used with a formal tool.

`include "prim_assert.sv"

module otbn_mai_assert_fpv
  import otbn_pkg::*;
#(
  parameter bit SecFixMaiOpSeq = 1'b0
) (
  input logic               clk_i,
  input logic               rst_ni,
  input logic               sec_wipe_mai_i,
  input logic               sec_wipe_running_i,
  input logic               ispr_mai_ctrl_wr_i,
  input logic [31:0]        ispr_mai_ctrl_wdata_i,
  input logic [31:0]        ispr_mai_ctrl_rdata_o,
  input logic [31:0]        ispr_mai_status_rdata_o,
  input logic               ispr_mai_in0_s0_wr_i,
  input logic               sec_wipe_ispr_mai_in0_s0_i,
  input logic [ExtWLEN-1:0] ispr_mai_in0_s0_wdata_i,
  input logic               ispr_mai_in0_s1_wr_i,
  input logic               sec_wipe_ispr_mai_in0_s1_i,
  input logic [ExtWLEN-1:0] ispr_mai_in0_s1_wdata_i,
  input logic               ispr_mai_in1_s0_wr_i,
  input logic               sec_wipe_ispr_mai_in1_s0_i,
  input logic [ExtWLEN-1:0] ispr_mai_in1_s0_wdata_i,
  input logic               ispr_mai_in1_s1_wr_i,
  input logic               sec_wipe_ispr_mai_in1_s1_i,
  input logic [ExtWLEN-1:0] ispr_mai_in1_s1_wdata_i,
  input logic               ispr_mai_res_s0_wr_i,
  input logic               sec_wipe_ispr_mai_res_s0_i,
  input logic [ExtWLEN-1:0] ispr_mai_res_s0_wdata_i,
  input logic               ispr_mai_res_s1_wr_i,
  input logic               sec_wipe_ispr_mai_res_s1_i,
  input logic [ExtWLEN-1:0] ispr_mai_res_s1_wdata_i,
  input logic [ExtWLEN-1:0] ispr_mai_in0_s0_rdata_o,
  input logic [ExtWLEN-1:0] ispr_mai_in0_s1_rdata_o,
  input logic [ExtWLEN-1:0] ispr_mai_in1_s0_rdata_o,
  input logic [ExtWLEN-1:0] ispr_mai_in1_s1_rdata_o,
  input logic [ExtWLEN-1:0] ispr_mai_res_s0_rdata_o,
  input logic [ExtWLEN-1:0] ispr_mai_res_s1_rdata_o,
  input logic [ExtWLEN-1:0] ispr_mod_intg_i,
  input logic               mai_software_error_o,
  input logic               mai_reg_intg_violation_err_o,
  input logic               mai_state_err_o,
  input logic [UrndLen-1:0] urnd_data_i
);

  ///////////////////////////////
  // Declarations & Parameters //
  ///////////////////////////////

  // Latency constants from the MAI spec (time from START until last result word written).
  // secAdd: 14 cycles, secAddMod: 22 cycles, A2B: 22 cycles, B2A: 23 cycles (no rejection).
  // Must be updated if any accelerator latency changes.
  localparam int unsigned MaiMaxDispatchCycles  = 8;  // 8-word sequential dispatch
  localparam int unsigned MaiMaxWritebackCycles = 8;  // 8-word sequential writeback
  localparam int unsigned MaiMinLatency         = 14; // secAdd — lower bound on busy duration
  localparam int unsigned MaiMaxLatency         = 23; // B2A without rejection — upper bound

  logic         mai_busy;
  logic         mai_ready;
  logic [4:0]   mai_operation;
  logic         mai_operation_valid;

  assign mai_busy          = ispr_mai_status_rdata_o[0];
  assign mai_ready         = ispr_mai_status_rdata_o[1];
  assign mai_operation     = ispr_mai_ctrl_wdata_i[5:1];
  assign mai_operation_valid = (mai_operation == ArithToBool) || (mai_operation == BoolToArith) ||
                               (mai_operation == SecAdd)      || (mai_operation == SecAddMod);

  /////////////////
  // Assumptions //
  /////////////////

  // `ASSUME(MyAssumption_M, ...)

  ////////////////////////
  // Forward Assertions //
  ////////////////////////

  // `ASSERT(MyFwdAssertion_A, ...)

  // CSR / WSR structure
  `ASSERT(MaiStatusRsvdBitsZero_A,   ispr_mai_status_rdata_o[31:2] == '0)
  `ASSERT(MaiCtrlRsvdBitsZero_A,     ispr_mai_ctrl_rdata_o[31:6] == '0)
  `ASSERT(MaiCtrlStartBitReadZero_A, ispr_mai_ctrl_rdata_o[0] == 1'b0)

  // Error handling
  `ASSERT(SwErrorInvldOpVals_A,
    ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] && !mai_operation_valid
    |=> $rose(mai_software_error_o))

  // Spec: "MAI_CTRL.START bit is set or MAI_CTRL.OPERATION is written to whilst BUSY = 1."
  `ASSERT(SwErrorFromCtrlWrWhileBusy_A,
    ispr_mai_ctrl_wr_i && mai_busy
    |=> $rose(mai_software_error_o))

  // Spec: "A write to the reserved section of MAI_CTRL is detected."
  `ASSERT(SwErrorFromRsvdCtrlWr_A,
    ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[31:6] != '0
    |=> $rose(mai_software_error_o))

  `ASSERT(SwErrorFromInsWrWhileNotReady_A,
    (ispr_mai_in0_s0_wr_i || ispr_mai_in0_s1_wr_i ||
     ispr_mai_in1_s0_wr_i || ispr_mai_in1_s1_wr_i) && !mai_ready
    |=> $rose(mai_software_error_o))

  // TODO: Add assertions for mai_reg_intg_violation_err_o and mai_state_err_o:
  // can multiple error outputs be simultaneously asserted? Does a register integrity
  // violation / state error result in a software error being raised?

  // MAI status register behaviour
  `ASSERT(AccelMustFinish_A, mai_busy |-> ##[1:MaiMaxLatency] !mai_busy)

  `ASSERT(StartBitSetsBusy_A,
    ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] && !mai_busy && mai_operation_valid
    |=> mai_busy)

  // MaiMinLatency (secAdd, 14 cycles) is the safe lower bound across all operation types;
  // using MaiMaxLatency here would incorrectly require secAdd to hold busy for 22 cycles.
  `ASSERT(BusyStaysHighDurOp_A,
    $rose(mai_busy) |-> mai_busy[*(MaiMinLatency - 1)])

  // MAI stops accepting new input once dispatch starts.
  `ASSERT(StartBitClearsReady_A,
    ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] && !mai_busy && mai_operation_valid
    |=> !mai_ready)

  // Dispatch consumes all eight 32-bit input words sequentially (one per cycle);
  // input WSRs are safe to overwrite only once all words are consumed.
  `ASSERT(ReadyReassertAfterDispatch_A,
    ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] && !mai_busy && mai_operation_valid
    |-> ##MaiMaxDispatchCycles mai_ready)

  // Secure wipe behaviour
  // SecWipeMaiStatusReset_A covers both BUSY=0 and READY=1 (bits [31:2] also zero).
  `ASSERT(SecWipeMaiStatusReset_A,
    sec_wipe_mai_i |=> ispr_mai_status_rdata_o == 32'h2)

  // Any in-progress operation is allowed to finish; rejection sampling for B2A is
  // disabled during wipe so 23 cycles remains the deterministic upper bound.
  `ASSERT(SecWipeAllowsExecToFinish_A,
    sec_wipe_running_i && mai_busy |-> ##[1:MaiMaxLatency] !mai_busy)

  // WSR stability: registers retain their value when neither written nor wiped.
  `ASSERT(In0S0Stable_A, !ispr_mai_in0_s0_wr_i && !sec_wipe_ispr_mai_in0_s0_i
    |=> $stable(ispr_mai_in0_s0_rdata_o))
  `ASSERT(In0S1Stable_A, !ispr_mai_in0_s1_wr_i && !sec_wipe_ispr_mai_in0_s1_i
    |=> $stable(ispr_mai_in0_s1_rdata_o))
  `ASSERT(In1S0Stable_A, !ispr_mai_in1_s0_wr_i && !sec_wipe_ispr_mai_in1_s0_i
    |=> $stable(ispr_mai_in1_s0_rdata_o))
  `ASSERT(In1S1Stable_A, !ispr_mai_in1_s1_wr_i && !sec_wipe_ispr_mai_in1_s1_i
    |=> $stable(ispr_mai_in1_s1_rdata_o))
  `ASSERT(ResS0Stable_A, !ispr_mai_res_s0_wr_i && !sec_wipe_ispr_mai_res_s0_i
    |=> $stable(ispr_mai_res_s0_rdata_o))
  `ASSERT(ResS1Stable_A, !ispr_mai_res_s1_wr_i && !sec_wipe_ispr_mai_res_s1_i
    |=> $stable(ispr_mai_res_s1_rdata_o))

  // WSR write-readback: written value must appear on readback the next cycle (FI detection).
  `ASSERT(In0S0WriteReadback_A,
    ispr_mai_in0_s0_wr_i && !sec_wipe_ispr_mai_in0_s0_i
    |=> ispr_mai_in0_s0_rdata_o == $past(ispr_mai_in0_s0_wdata_i))
  `ASSERT(In0S1WriteReadback_A,
    ispr_mai_in0_s1_wr_i && !sec_wipe_ispr_mai_in0_s1_i
    |=> ispr_mai_in0_s1_rdata_o == $past(ispr_mai_in0_s1_wdata_i))
  `ASSERT(In1S0WriteReadback_A,
    ispr_mai_in1_s0_wr_i && !sec_wipe_ispr_mai_in1_s0_i
    |=> ispr_mai_in1_s0_rdata_o == $past(ispr_mai_in1_s0_wdata_i))
  `ASSERT(In1S1WriteReadback_A,
    ispr_mai_in1_s1_wr_i && !sec_wipe_ispr_mai_in1_s1_i
    |=> ispr_mai_in1_s1_rdata_o == $past(ispr_mai_in1_s1_wdata_i))
  `ASSERT(ResS0WriteReadback_A,
    ispr_mai_res_s0_wr_i && !sec_wipe_ispr_mai_res_s0_i
    |=> ispr_mai_res_s0_rdata_o == $past(ispr_mai_res_s0_wdata_i))
  `ASSERT(ResS1WriteReadback_A,
    ispr_mai_res_s1_wr_i && !sec_wipe_ispr_mai_res_s1_i
    |=> ispr_mai_res_s1_rdata_o == $past(ispr_mai_res_s1_wdata_i))

  // Result WSRs must be written by the accelerator within MaiMaxLatency cycles of starting.
  `ASSERT(ResS0WrittenDuringOp_A,
    $rose(mai_busy) |-> ##[1:MaiMaxLatency] ispr_mai_res_s0_wr_i)
  `ASSERT(ResS1WrittenDuringOp_A,
    $rose(mai_busy) |-> ##[1:MaiMaxLatency] ispr_mai_res_s1_wr_i)

  /////////////
  // Covers  //
  /////////////

  // Busy / ready state reachability
  `COVER(mai_status_is_busy_C, mai_busy)
  `COVER(mai_status_is_not_busy_C, !mai_busy)
  `COVER(accel_finished_C, $fell(mai_busy))
  `COVER(mai_status_is_ready_C, mai_ready)
  `COVER(mai_status_is_not_ready_C, !mai_ready)
  `COVER(mai_status_is_busy_and_ready_C, mai_busy && mai_ready)

  // Error signal reachability
  `COVER(mai_sw_err_seen_C, $rose(mai_software_error_o))
  `COVER(mai_reg_intg_violation_seen_C, $rose(mai_reg_intg_violation_err_o))
  `COVER(mai_state_err_seen_C, $rose(mai_state_err_o))

  // One cover per operation type for basic functional reachability
  `COVER(SecAddStarted_C, ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] && !mai_busy && mai_operation == SecAdd)
  `COVER(SecAddModStarted_C, ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] && !mai_busy && mai_operation == SecAddMod)
  `COVER(ArithToBoolStarted_C, ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] && !mai_busy && mai_operation == ArithToBool)
  `COVER(BoolToArithStarted_C, ispr_mai_ctrl_wr_i && ispr_mai_ctrl_wdata_i[0] && !mai_busy && mai_operation == BoolToArith)

  // Secure wipe reachability for all WSRs (input and result)
  `COVER(SecWipeIn0S0Reached_C, sec_wipe_ispr_mai_in0_s0_i)
  `COVER(SecWipeIn0S1Reached_C, sec_wipe_ispr_mai_in0_s1_i)
  `COVER(SecWipeIn1S0Reached_C, sec_wipe_ispr_mai_in1_s0_i)
  `COVER(SecWipeIn1S1Reached_C, sec_wipe_ispr_mai_in1_s1_i)
  `COVER(SecWipeResS0Reached_C, sec_wipe_ispr_mai_res_s0_i)
  `COVER(SecWipeResS1Reached_C, sec_wipe_ispr_mai_res_s1_i)

endmodule : otbn_mai_assert_fpv
