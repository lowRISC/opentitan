// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager top level
//

`include "prim_assert.sv"

module keymgr_ctrl import keymgr_pkg::*;(
  input clk_i,
  input rst_ni,

  // lifecycle enforcement
  input keymgr_en_i,

  // entropy input
  input [(LfsrWidth/2)-1:0] entropy_i,
  output logic prng_en_o,

  // Software interface
  input init_i,
  output logic init_done_o,
  input op_start_i,
  input keymgr_ops_e op_i,
  output logic op_done_o,
  output keymgr_op_status_e status_o,
  output logic [ErrLastPos-1:0] error_o,
  output logic data_valid_o,
  output keymgr_working_state_e working_state_o,

  // Data input
  input  [KeyWidth-1:0] root_key_i,
  output keymgr_gen_out_e hw_sel_o,
  output keymgr_stage_e stage_sel_o,

  // KMAC ctrl interface
  output logic adv_en_o,
  output logic id_en_o,
  output logic gen_en_o,
  output logic [Shares-1:0][KeyWidth-1:0] key_o,
  output logic load_key_o,
  input kmac_done_i,
  input kmac_input_invalid_i, // asserted when selected data fails criteria check
  input kmac_fsm_err_i, // asserted when kmac fsm reaches unexpected state
  input kmac_cmd_err_i, // asserted when more than one command given to kmac
  input [Shares-1:0][KeyWidth-1:0] kmac_data_i
);
  localparam int EntropyWidth = LfsrWidth / 2;
  localparam int EntropyRounds = KeyWidth / EntropyWidth;
  localparam int CntWidth = $clog2(EntropyRounds + 1);

  keymgr_working_state_e state_q, state_d;
  logic [Shares-1:0][EntropyRounds-1:0][EntropyWidth-1:0] key_state_q, key_state_d;

  logic [CntWidth-1:0] cnt;
  logic cnt_en;
  logic cnt_clr;
  logic data_valid;
  logic adv_en_q;
  logic op_accepted;
  logic invalid_op;

  // disable is treated like an advanced call
  logic advance_sel;
  logic disable_sel;
  logic gen_id_sel;
  logic gen_out_sw_sel;
  logic gen_out_hw_sel;
  logic gen_out_sel;
  logic gen_sel;

  // something went wrong with the kmac interface operation
  logic kmac_op_err;

  assign advance_sel    = op_i == OpAdvance  & keymgr_en_i;
  assign gen_id_sel     = op_i == OpGenId    & keymgr_en_i;
  assign gen_out_sw_sel = op_i == OpGenSwOut & keymgr_en_i;
  assign gen_out_hw_sel = op_i == OpGenHwOut & keymgr_en_i;
  assign gen_out_sel    = gen_out_sw_sel | gen_out_hw_sel;
  assign gen_sel        = gen_id_sel | gen_out_sel;

  // disable is selected whenever a normal operation is not, and when
  // keymgr is disabled
  assign disable_sel    = !(gen_sel | advance_sel) | !keymgr_en_i;

  assign adv_en_o   = op_accepted & (advance_sel | disable_sel);
  assign id_en_o    = op_accepted & gen_id_sel;
  assign gen_en_o   = op_accepted & gen_out_sel;
  assign load_key_o = adv_en_o & !adv_en_q;

  // check incoming kmac data validity
  // also check inputs used during compute
  assign data_valid = valid_data_chk(kmac_data_i[0]) & valid_data_chk(kmac_data_i[1])
    & !kmac_input_invalid_i & !kmac_op_err;

  // Unlike the key state, the working state can be safely reset.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StReset;
      adv_en_q <= 1'b0;
    end else begin
      state_q <= state_d;
      adv_en_q <= adv_en_o;
    end
  end

  // prevents unknowns from reaching the outside world.
  // whatever operation causes the input data select to be disabled should
  // also not expose the key state
  assign key_o = disable_sel ? {EntropyRounds * Shares {entropy_i}} : key_state_q;

  // key state is intentionally not reset
  always_ff @(posedge clk_i) begin
    key_state_q <= key_state_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
    end else if (cnt_clr) begin
      cnt <= '0;
    end else if (cnt_en) begin
      cnt <= cnt + 1'b1;
    end
  end

  assign kmac_op_err = kmac_cmd_err_i | kmac_fsm_err_i;

  always_comb begin
    // persistent data
    state_d = state_q;
    key_state_d = key_state_q;

    // locally consumed select signals
    cnt_en = 1'b0;
    cnt_clr = 1'b0;
    op_accepted = 1'b0;
    invalid_op = 1'b0;

    // data update and select signals
    hw_sel_o = HwKey;
    stage_sel_o = Disable;

    // enable prng toggling
    prng_en_o = 1'b1;

    op_done_o = 1'b0;
    init_done_o = 1'b0;

    // TBD
    // Wait for some more software feedback to see if the states remain so similar.
    // If yes, we can merge 3 states below with some minor tweaking.
    unique case (state_q)
      // This state does not accept any command. Issuing any command
      // will cause an immediate error
      StReset: begin
        // in reset state, don't enable entropy yet, since there are no users.
        // long term, this should be replaced by a req/ack with csrng
        prng_en_o = 1'b0;
        op_done_o = op_start_i;
        invalid_op = op_start_i;

        // When initialization command is given, begin.
        // Note, if init is called at the same time as start, it is considered
        // an invalid command sequence.
        if (init_i && !invalid_op && keymgr_en_i) begin
          state_d = StWipe;
        end else begin
          state_d = StReset;
          init_done_o = init_i & invalid_op;
        end
      end

      // This state does not accept any command.
      StWipe: begin
        // populate both shares with the same entropy
        // This is the default mask
        if (cnt < EntropyRounds) begin
          cnt_en = 1'b1;
          for (int i = 0; i < Shares; i++) begin
            key_state_d[i][cnt] = entropy_i;
          end
        end
        // when mask population is complete, xor the root_key into the zero share
        // if in the future the root key is updated to 2 shares, it will direclty overwrite
        // the values here
        else begin
          cnt_clr = 1'b1;
          key_state_d[0] = key_state_q[0] ^ root_key_i;
          init_done_o = 1'b1;
          state_d = StInit;
        end
      end

      // Beginning from the Init state, operations are accepted.
      // Only valid operation is advance state. If invalid command received,
      // random data is selected for operation and no persistent state is changed.
      StInit: begin
        op_done_o = op_start_i & kmac_done_i;

        if (op_start_i || !keymgr_en_i) begin
          op_accepted = 1'b1;
          stage_sel_o = !advance_sel ? Disable : Creator;
        end

        // key state is updated when it is an advance call
        if (op_done_o && (disable_sel || kmac_op_err)) begin
          key_state_d = kmac_data_i;
          state_d = StDisabled;
        end else if (op_done_o && advance_sel) begin
          key_state_d = data_valid ? kmac_data_i : key_state_q;
          state_d = StCreatorRootKey;
        end else if (op_done_o) begin
          invalid_op = 1'b1;
        end
      end

      // all commands are valid during this stage
      StCreatorRootKey: begin
        op_done_o = op_start_i & kmac_done_i;

        // when generating, select creator data input
        // when advancing, select owner intermediate key as target
        // when disabling, select random data input

        if (op_start_i || !keymgr_en_i) begin
          op_accepted = 1'b1;
          stage_sel_o = disable_sel ? Disable  :
                        advance_sel ? OwnerInt : Creator;
          hw_sel_o = gen_out_hw_sel ? HwKey : SwKey;
        end

        // key state is updated when it is an advance call
        if (op_done_o && (disable_sel || kmac_op_err)) begin
          key_state_d = kmac_data_i;
          state_d = StDisabled;
        end else if (op_done_o && advance_sel) begin
          key_state_d = data_valid ? kmac_data_i : key_state_q;
          state_d = StOwnerIntKey;
        end
      end


      // all commands are valid during this stage
      StOwnerIntKey: begin
        op_done_o = op_start_i & kmac_done_i;

        // when generating, select creator data input
        // when advancing, select owner intermediate key as target
        // when disabling, select random data input
        if (op_start_i || !keymgr_en_i) begin
          op_accepted = 1'b1;
          stage_sel_o = disable_sel ? Disable  :
                        advance_sel ? Owner : OwnerInt;
          hw_sel_o = gen_out_hw_sel ? HwKey : SwKey;
        end

        if (op_done_o && (disable_sel || kmac_op_err)) begin
          key_state_d = kmac_data_i;
          state_d = StDisabled;
        end else if (op_done_o && advance_sel) begin
          key_state_d = data_valid ? kmac_data_i : key_state_q;
          state_d = StOwnerKey;
        end
      end

      // all commands are valid during this stage
      // however advance goes directly to disabled state
      StOwnerKey: begin
        op_done_o = op_start_i & kmac_done_i;

        if (op_start_i || !keymgr_en_i) begin
          op_accepted = 1'b1;
          stage_sel_o = disable_sel || advance_sel  ? Disable : Owner;
          hw_sel_o = gen_out_hw_sel ? HwKey : SwKey;
        end

        // Calling advanced from ownerKey also leads to disable
        // Thus data_valid is not checked
        if (op_done_o && (advance_sel || disable_sel || kmac_op_err)) begin
          key_state_d = kmac_data_i;
          state_d = StDisabled;
        end
      end

      // Terminal state (StDisabled is included)
      // However, it will continue to kick off dummy transactions
      default: begin
        op_done_o = op_start_i & kmac_done_i;

        // accept any command, but always select fake data
        op_accepted = op_start_i;
        stage_sel_o = Disable;
        hw_sel_o = gen_out_hw_sel ? HwKey : SwKey;

        // During disabled state, continue to update state
        key_state_d = (op_done_o && advance_sel) ? kmac_data_i : key_state_q;

        // Despite accepting all commands, operations are always
        // considered invalid in disabled state
        // TBD this may be changed later if we decide to hide disable state from
        // software.
        invalid_op = op_start_i;
      end

    endcase // unique case (state_q)
  end


  // Current working state provided for software read
  assign working_state_o = state_q;

  // if operation was never accepted (ie a generate was called in StReset / StWipe), then
  // never update the sw / hw outputs when operation is complete
  assign data_valid_o = op_done_o & op_accepted & data_valid & gen_sel;

  // data errors are not relevant when operation was not accepted.
  assign error_o[ErrInvalidOp]  = invalid_op;
  assign error_o[ErrInvalidCmd] = op_start_i & op_accepted & kmac_op_err;
  assign error_o[ErrInvalidIn]  = op_done_o & op_accepted & kmac_input_invalid_i;
  assign error_o[ErrInvalidOut] = op_done_o & op_accepted & ~data_valid;

  always_comb begin
    status_o = OpIdle;
    if (op_done_o) begin
      status_o = |error_o ? OpDoneFail : OpDoneSuccess;
    end else if (op_start_i) begin
      status_o = OpWip;
    end
  end



  ///////////////////////////////
  // Functions
  ///////////////////////////////

  // unclear what this is supposed to be yet
  // right now just check to see if it not all 0's and not all 1's
  function automatic logic valid_data_chk (logic [KeyWidth-1:0] value);

    return |value & ~&value;

  endfunction // byte_mask

endmodule
