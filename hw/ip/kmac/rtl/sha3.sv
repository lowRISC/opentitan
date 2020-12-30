// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SHA3 core is a fully functional SHA3/SHAKE/cSHAKE hashing module.
//
// It instantiates a keccak_round with 1600 bits of the state.

`include "prim_assert.sv"

module sha3
  import sha3_pkg::*;
#(
  // Enable Masked Keccak if 1
  parameter  bit EnMasking = 0,
  // derived parameter
  localparam int Share = (EnMasking) ? 2 : 1,

  // Configurations
  // Decide if implements Re-use the adjacent shares as entropy
  // in DOM AND logic
  parameter bit ReuseShare = 0
) (
  input clk_i,
  input rst_ni,

  // MSG interface
  input                       msg_valid_i,
  input        [MsgWidth-1:0] msg_data_i [Share],
  input        [MsgStrbW-1:0] msg_strb_i,         // one strobe for shares
  output logic                msg_ready_o,

  // Entropy interface
  input                     rand_valid_i,
  input        [StateW-1:0] rand_data_i,
  output logic              rand_consumed_o,

  // N, S: Used in cSHAKE mode only
  input [NSRegisterSize*8-1:0] ns_data_i, // See sha3_pkg for details

  // configurations
  input sha3_mode_e       mode_i,     // see sha3pad for details
  input keccak_strength_e strength_i, // see sha3pad for details

  // controls
  input start_i,   // see sha3pad for details
  input process_i, // see sha3pad for details

  // run_i is a pulse signal to trigger the keccak_round manually by SW.
  // It is used to run additional keccak_f after sponge absorbing is completed.
  // See `keccak_run` signal
  input run_i,
  input done_i,    // see sha3pad for details

  output logic absorbed_o,
  output logic squeezing_o,

  // Indicate of one block processed. KMAC main state tracks the progression
  // based on this signal.
  output logic block_processed_o,

  output sha3_st_e sha3_fsm_o,

  // digest output
  // This value is valid only after all absorbing process is completed.
  // In invalid state, the output `state` will be zero to prevent information
  // leakage.
  output logic              state_valid_o,
  output logic [StateW-1:0] state_o [Share],

  // error_o value is pushed to Error FIFO at KMAC/SHA3 top and reported to SW
  output err_t error_o
);
  /////////////////
  // Definitions //
  /////////////////

  typedef enum logic[2:0] {
    MuxGuard   = 3'b 010,
    MuxRelease = 3'b 101
  } state_mux_sel_e;

  /////////////
  // Signals //
  /////////////

  // State --> Digest
  // State is exposed to the outside if the hashing process is completed.
  logic              state_valid;
  logic [StateW-1:0] state [Share];
  logic [StateW-1:0] state_guarded [Share];

  // State --> digest mux select signal
  state_mux_sel_e mux_sel;

  // absorbed is a pulse signal that indicates sponge absorbing is done.
  // After this, sha3 core allows software to manually run until squeezing
  // is completed, which is the `done_i` pulse signal.
  logic absorbed;

  // `squeezing` is a status indicator that SHA3 core is in sponge squeezing
  // stage. In this stage, the state output is valid, and software can manually
  // trigger keccak_round logic to get more digest outputs in case the output
  // length is bigger than the block limit.
  logic squeezing;

  // FSM variable
  sha3_pkg::sha3_st_e st, st_d;

  // Keccak control signal (filtered by State Machine)
  logic keccak_start, keccak_process, keccak_done;

  /////////////////
  // Connections //
  /////////////////

  logic                       keccak_valid;
  logic [KeccakMsgAddrW-1:0]  keccak_addr;
  logic [MsgWidth-1:0]        keccak_data [Share];
  logic                       keccak_ready;

  // Keccak round run signal can be controlled by sha3pad and also by software
  // after all message feeding is done. it is mainly used for sponge squeezing
  // operation after absorbing is completed when output length is longer than
  // the block size.
  logic keccak_run, sha3pad_keccak_run, sw_keccak_run;
  logic keccak_complete;

  assign keccak_run = sha3pad_keccak_run | sw_keccak_run;

  // Absorb pulse output : used to generate interrupts
  assign absorbed_o = absorbed;

  // Squeezing output
  assign squeezing_o = squeezing;

  assign block_processed_o = keccak_complete;

  // State connection
  assign state_valid_o = state_valid;
  assign state_o = state_guarded;

  assign sha3_fsm_o = st;

  ///////////////////
  // State Machine //
  ///////////////////

  // State Register
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st <= StIdle;
    else         st <= st_d;
  end

  // Next State and Output Logic
  // Mainly the FSM controls the input signal access
  // StIdle:    only start_i signal is allowed
  // StAbsorb:  only process_i signal is allowed
  // StSqueeze: only run_i, done_i signal is allowed

  always_comb begin
    st_d = StIdle;

    // default output values
    keccak_start = 1'b 0;
    keccak_process = 1'b 0;
    sw_keccak_run = 1'b 0;
    keccak_done = 1'b 0;

    squeezing = 1'b 0;

    state_valid = 1'b 0;
    mux_sel = MuxGuard ;

    unique case (st)
      StIdle: begin
        if (start_i) begin
          st_d = StAbsorb;

          keccak_start = 1'b 1;
        end else begin
          st_d = StIdle;
        end
      end

      StAbsorb: begin
        if (process_i) begin
          st_d = StAbsorb;

          keccak_process = 1'b 1;
        // TODO: Software Cancellation here? in case of absorbed not asserted
        end else if (absorbed) begin
          st_d = StSqueeze;
        end else begin
          st_d = StAbsorb;
        end
      end

      StSqueeze: begin
        state_valid = 1'b 1;
        mux_sel = MuxRelease; // Expose state to register interface

        squeezing = 1'b 1;

        if (run_i) begin
          st_d = StManualRun;

          sw_keccak_run = 1'b 1;
        end else if (done_i) begin
          st_d = StFlush;

          keccak_done = 1'b 1;
        end else begin
          st_d = StSqueeze;
        end
      end

      StManualRun: begin
        // TODO: Software cancellation here?
        if (keccak_complete) begin
          st_d = StSqueeze;
        end else begin
          st_d = StManualRun;
        end
      end

      StFlush: begin
        st_d = StIdle;
      end

      default: begin
        st_d = StIdle;
      end

    endcase
  end

  //////////////
  // Datapath //
  //////////////

  // State --> Digest output
  always_comb begin : state_guarded_mux
    unique case (mux_sel)
      MuxGuard:   state_guarded = '{default: '0};
      MuxRelease: state_guarded = state;
      default:    state_guarded = '{default: '0}; // a valid, safe output
    endcase
  end


  // Error Detecting
  // ErrSha3SwControl:
  //   info[ 0]: start_i set
  //   info[ 1]: process_i set
  //   info[ 2]: run_i set
  //   info[ 3]: done_i set
  //  - Sw set process_i, run_i, done_i without start_i

  always_comb begin
    error_o.valid = 1'b 0;
    error_o.code  = ErrNone;
    error_o.info  = '0;

    unique case (st)
      StIdle: begin
        if (process_i || run_i || done_i) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({done_i, run_i, process_i, start_i})
          };
        end
      end

      StAbsorb: begin
        if (start_i || run_i || done_i) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({done_i, run_i, process_i, start_i})
          };
        end
      end

      StSqueeze: begin
        if (start_i || process_i) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({done_i, run_i, process_i, start_i})
          };
        end
      end

      StManualRun: begin
        if (start_i || process_i || run_i || done_i) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({done_i, run_i, process_i, start_i})
          };
        end
      end

      StFlush: begin
        if (start_i || process_i || run_i || done_i) begin
          error_o = '{
            valid: 1'b 1,
            code: ErrSha3SwControl,
            info: 24'({done_i, run_i, process_i, start_i})
          };
        end
      end

      default: begin
      end
    endcase
  end
  ///////////////
  // Instances //
  ///////////////

  // SHA3 pad logic
  sha3pad #(
    .EnMasking (EnMasking)
  ) u_pad (
    .clk_i,
    .rst_ni,

    // MSG_FIFO (or from KMAC core)
    .msg_valid_i,
    .msg_data_i, // [Share]
    .msg_strb_i,
    .msg_ready_o,

    // Encoded N, S
    .ns_data_i,

    // output to keccak_round: message path
    .keccak_valid_o (keccak_valid),
    .keccak_addr_o  (keccak_addr ),
    .keccak_data_o  (keccak_data ), // [Share]
    .keccak_ready_i (keccak_ready),

    .keccak_run_o      (sha3pad_keccak_run),
    .keccak_complete_i (keccak_complete   ),

    // configurations
    .mode_i,
    .strength_i,

    // controls
    .start_i   (keccak_start),
    .process_i (keccak_process),
    .done_i    (keccak_done),

    // output
    .absorbed_o (absorbed)
  );

  // Keccak round logic
  keccak_round #(
    .Width    (sha3_pkg::StateW),
    .DInWidth (sha3_pkg::MsgWidth),

    .EnMasking  (EnMasking),
    .ReuseShare (ReuseShare)
  ) u_keccak (
    .clk_i,
    .rst_ni,

    .valid_i (keccak_valid),
    .addr_i  (keccak_addr ),
    .data_i  (keccak_data ),
    .ready_o (keccak_ready),

    .rand_valid_i,
    .rand_data_i,
    .rand_consumed_o,

    .run_i      (keccak_run     ),
    .complete_o (keccak_complete),

    .state_o    (state),

    .clear_i    (keccak_done)
  );

  ////////////////
  // Assertions //
  ////////////////

  // Unknown check for case statement
  `ASSERT(MuxSelKnown_A, mux_sel inside {MuxGuard, MuxRelease})
  `ASSERT(FsmKnown_A, st inside {StIdle, StAbsorb, StSqueeze, StManualRun, StFlush})

  // `state` shall be 0 in invalid
  if (EnMasking) begin: gen_chk_digest_masked
    `ASSERT(StateZeroInvalid_A, !state_valid_o |-> ((|state_o[0]) | (|state_o[1])) == 1'b 0)
  end else begin : gen_chk_digest_unmasked
    `ASSERT(StateZeroInvalid_A, !state_valid_o |-> (|state_o[0]) == 1'b 0)
  end

  // `state_valid_o` asserts only in between the completion and done
  //`ASSERT(StateValidPeriod_A, state_valid_o |-> )

  // skip the msg interface assertions as they are in sha3pad.sv

  // Software run signal happens in Squeezing stage
  `ASSUME(SwRunInSqueezing_a, run_i |-> error_o.valid || (st == StSqueeze))

  // If control received but not propagated into submodules, it is error condition
  `ASSERT(ErrDetection_A, error_o.valid
    |-> {start_i,      process_i,      run_i,         done_i}
     != {keccak_start, keccak_process, sw_keccak_run, keccak_done})

endmodule

