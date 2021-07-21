// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager top level
//

`include "prim_assert.sv"

module keymgr_ctrl import keymgr_pkg::*; (
  input clk_i,
  input rst_ni,

  // lifecycle enforcement
  input en_i,

  // Software interface
  input op_start_i,
  input keymgr_ops_e op_i,
  input [CdiWidth-1:0] op_cdi_sel_i,
  output logic op_done_o,
  output keymgr_op_status_e status_o,
  output logic [ErrLastPos-1:0] error_o,
  output logic data_en_o,
  output logic data_valid_o,
  output logic wipe_key_o,
  output keymgr_working_state_e working_state_o,
  output logic sw_binding_unlock_o,
  output logic init_o,

  // Data input
  input  otp_ctrl_pkg::otp_keymgr_key_t root_key_i,
  output keymgr_gen_out_e hw_sel_o,
  output keymgr_stage_e stage_sel_o,
  output logic [CdiWidth-1:0] cdi_sel_o,

  // KMAC ctrl interface
  output logic adv_en_o,
  output logic id_en_o,
  output logic gen_en_o,
  output hw_key_req_t key_o,
  input kmac_done_i,
  input kmac_input_invalid_i, // asserted when selected data fails criteria check
  input kmac_fsm_err_i, // asserted when kmac fsm reaches unexpected state
  input kmac_op_err_i,  // asserted when kmac itself reports an error
  input kmac_cmd_err_i, // asserted when more than one command given to kmac
  input [Shares-1:0][KeyWidth-1:0] kmac_data_i,

  // prng control interface
  input [Shares-1:0][RandWidth-1:0] entropy_i,
  input prng_reseed_ack_i,
  output logic prng_reseed_req_o,
  output logic prng_en_o
);

  localparam int EntropyWidth = LfsrWidth / 2;
  localparam int EntropyRounds = KeyWidth / EntropyWidth;
  localparam int EntropyRndWidth = prim_util_pkg::vbits(EntropyRounds);
  localparam int CntWidth = EntropyRounds > CDIs ? EntropyRndWidth : CdiWidth;

  // Enumeration for working state
  typedef enum logic [3:0] {
    StCtrlReset,
    StCtrlEntropyReseed,
    StCtrlRandom,
    StCtrlRootKey,
    StCtrlInit,
    StCtrlCreatorRootKey,
    StCtrlOwnerIntKey,
    StCtrlOwnerKey,
    StCtrlDisabled,
    StCtrlWipe,
    StCtrlInvalid
  } keymgr_ctrl_state_e;

  // Enumeration for operation handling
  typedef enum logic [2:0] {
    StIdle,
    StRandomize,
    StAdv,
    StAdvAck,
    StWait
  } keymgr_op_state_e;

  keymgr_ctrl_state_e state_q, state_d;
  keymgr_op_state_e op_state_q, op_state_d;

  // There are two versions of the key state, one for sealing one for attestation
  // Among each version, there are multiple shares
  // Each share is a fixed multiple of the entropy width
  logic [CDIs-1:0][Shares-1:0][EntropyRounds-1:0][EntropyWidth-1:0] key_state_q, key_state_d;
  logic [CntWidth-1:0] cnt;
  logic [CdiWidth-1:0] cdi_cnt;

  logic key_update;
  logic data_update;
  logic kmac_out_valid;
  logic invalid_op;
  logic disabled;

  // disable is treated like an advanced call
  logic advance_sel;
  logic disable_sel;
  logic gen_id_sel;
  logic gen_out_sw_sel;
  logic gen_out_hw_sel;
  logic gen_out_sel;
  logic gen_sel;

  // error types
  logic op_err;
  logic fault_err;
  logic fault_err_q;
  logic fault_err_d;

  assign fault_err = fault_err_q | fault_err_d;

  // req/ack interface with op handling fsm
  logic op_req;
  logic op_ack;
  logic op_update;
  logic random_req;
  logic random_ack;

  // req from main control fsm to key update controls
  logic wipe_req;

  assign advance_sel    = op_start_i & op_i == OpAdvance  & en_i;
  assign gen_id_sel     = op_start_i & op_i == OpGenId    & en_i;
  assign gen_out_sw_sel = op_start_i & op_i == OpGenSwOut & en_i;
  assign gen_out_hw_sel = op_start_i & op_i == OpGenHwOut & en_i;
  assign gen_out_sel    = gen_out_sw_sel | gen_out_hw_sel;
  assign gen_sel        = gen_id_sel | gen_out_sel;

  // disable is selected whenever a normal operation is not, and when
  // keymgr is disabled
  assign disable_sel    = (op_start_i & !(gen_sel | advance_sel)) |
                          !en_i;

  // requestion from working state to operation handling FSM
  logic adv_req, id_req, gen_req;
  assign adv_req    = op_req & (advance_sel | disable_sel);
  assign id_req     = op_req & gen_id_sel;
  assign gen_req    = op_req & gen_out_sel;

  // unlock sw binding configuration whenever an advance call is made without errors
  assign sw_binding_unlock_o = adv_en_o & op_ack & ~|error_o;

  // check incoming kmac data validity
  assign kmac_out_valid = valid_data_chk(kmac_data_i[0]) & valid_data_chk(kmac_data_i[1]);

  // error definition
  assign fault_err_d = kmac_cmd_err_i | kmac_fsm_err_i | kmac_op_err_i | ~kmac_out_valid;
  assign op_err = kmac_input_invalid_i | invalid_op;

  // key update conditions
  assign key_update = (op_ack | op_update) & (advance_sel | disable_sel);

  // external collateral update conditions
  assign data_update = op_ack & gen_sel;

  // Unlike the key state, the working state can be safely reset.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StCtrlReset;
      op_state_q <= StIdle;
    end else begin
      state_q <= state_d;
      op_state_q <= op_state_d;
    end
  end

  // prevents unknowns from reaching the outside world.
  // - whatever operation causes the input data select to be disabled should not expose the key
  //   state.
  // - when there are no operations, the key state also should be exposed.
  assign key_o.valid = op_req;
  assign cdi_sel_o = advance_sel ? cdi_cnt : op_cdi_sel_i;

  for (genvar i = 0; i < Shares; i++) begin : gen_key_out_assign
    assign key_o.key[i] = stage_sel_o == Disable ?
                          {EntropyRounds{entropy_i[i]}} :
                          key_state_q[cdi_sel_o][i];
  end


  // key state is intentionally not reset
  always_ff @(posedge clk_i) begin
    key_state_q <= key_state_d;
  end

  // root key valid sync
  logic root_key_valid_q;

  prim_flop_2sync # (
    .Width(1)
  ) u_key_valid_sync (
    .clk_i,
    .rst_ni,
    .d_i(root_key_i.valid),
    .q_o(root_key_valid_q)
  );

  keymgr_key_update_e update_sel, op_update_sel;
  logic key_update_vld;

  assign update_sel = wipe_req ? KeyUpdateWipe :
                      init_o   ? KeyUpdateRoot : op_update_sel;

  // Do not let the count toggle unless an advance operation is
  // selected
  assign cdi_cnt = op_req ? cnt[CdiWidth-1:0] : '0;

  always_comb begin
    key_state_d = key_state_q;
    data_valid_o = 1'b0;
    wipe_key_o = 1'b0;
    key_update_vld = 1'b0;


    // if a wipe request arrives, immediately destroy the
    // keys regardless of current state

    unique case (update_sel)
      KeyUpdateRandom: begin
        for (int i = 0; i < CDIs; i++) begin
          for (int j = 0; j < Shares; j++) begin
            key_state_d[i][j][cnt[EntropyRndWidth-1:0]] = entropy_i[j];
          end
        end
      end

      KeyUpdateRoot: begin
        if (root_key_valid_q) begin
          for (int i = 0; i < CDIs; i++) begin
            key_state_d[i][0] = root_key_i.key_share0;
            key_state_d[i][1] = root_key_i.key_share1;
          end
        end
      end

      KeyUpdateKmac: begin
        data_valid_o = data_update & ~fault_err & ~op_err;
        key_update_vld = key_update & ~fault_err & ~op_err;
        key_state_d[cdi_sel_o] = key_update_vld ? kmac_data_i : key_state_q[cdi_sel_o];
      end

      KeyUpdateInvalid: begin
        data_valid_o = data_update;
        key_update_vld = key_update;
        key_state_d[cdi_sel_o] = key_update_vld ? kmac_data_i : key_state_q[cdi_sel_o];
      end

      KeyUpdateWipe: begin
        wipe_key_o = 1'b1;
        for (int i = 0; i < CDIs; i++) begin
          for (int j = 0; j < Shares; j++) begin
            key_state_d[i][j] = {EntropyRounds{entropy_i[j]}};
          end
        end
      end

      default:;
    endcase // unique case (update_sel)
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= '0;
    end else if (op_ack || random_ack) begin
      cnt <= '0;
    end else if (op_update) begin
      cnt <= cnt + 1'b1;
    end
  end

  // TODO: Create a no select option, do not leave this as binary
  assign hw_sel_o = gen_out_hw_sel ? HwKey : SwKey;


  // when in a state that accepts commands, look at op_ack for completion
  // when in a state that does not accept commands, wait for other triggers.
  assign op_done_o = op_req ? op_ack :
                     (init_o | invalid_op);


  logic next_state;
  logic invalid_state;
  assign next_state = op_ack & advance_sel & key_update_vld;
  assign invalid_state = op_ack & (disable_sel | fault_err);


  always_comb begin
    // persistent data
    state_d = state_q;

    // request to op handling
    op_req = 1'b0;
    random_req = 1'b0;

    // request to key updates
    wipe_req = 1'b0;

    // invalid operation issued
    invalid_op = 1'b0;

    // data update and select signals
    stage_sel_o = Disable;

    // enable prng toggling
    prng_reseed_req_o = 1'b0;
    prng_en_o = 1'b0;

    // initialization complete
    init_o = 1'b0;

    // Indicates the control state machine is disabled
    disabled = 1'b0;

    unique case (state_q)
      // Only advance can be called from reset state
      StCtrlReset: begin
        // in reset state, don't enable entropy yet, since there are no users.
        prng_en_o = 1'b0;

        // always use random data for advance, since out of reset state
        // the key state will be randomized.
        stage_sel_o = Disable;

        // key state is updated when it is an advance call
        // all other operations are invalid, including disable
        if (advance_sel) begin
          state_d = StCtrlEntropyReseed;
        end else if (op_start_i) begin
          invalid_op = 1'b1;
        end
      end

      // reseed entropy
      StCtrlEntropyReseed: begin
        prng_reseed_req_o = 1'b1;
        if (prng_reseed_ack_i) begin
          state_d = StCtrlRandom;
        end
      end

      // This state does not accept any command.
      StCtrlRandom: begin
        prng_en_o = 1'b1;
        random_req = 1'b1;

        if (random_ack) begin
          state_d = StCtrlRootKey;
        end
      end

      // load the root key.
      StCtrlRootKey: begin
        init_o = 1'b1;
        state_d = StCtrlInit;
      end

      // Beginning from the Init state, operations are accepted.
      // Only valid operation is advance state. If invalid command received,
      // random data is selected for operation and no persistent state is changed.
      StCtrlInit: begin
        op_req = op_start_i;

        // when advancing select creator data, otherwise use random input
        stage_sel_o = advance_sel ? Creator : Disable;
        invalid_op = op_start_i & ~(advance_sel | disable_sel);

        if (!en_i) begin
          state_d = StCtrlWipe;
        end else if (invalid_state) begin
          state_d = StCtrlDisabled;
        end else if (next_state) begin
          state_d = StCtrlCreatorRootKey;
        end
      end

      // all commands  are valid during this stage
      StCtrlCreatorRootKey: begin
        op_req = op_start_i;

        // when generating, select creator data input
        // when advancing, select owner intermediate key as target
        // when disabling, select random data input
        stage_sel_o = disable_sel ? Disable  :
                      advance_sel ? OwnerInt : Creator;

        if (!en_i) begin
          state_d = StCtrlWipe;
        end else if (invalid_state) begin
          state_d = StCtrlDisabled;
        end else if (next_state) begin
          state_d = StCtrlOwnerIntKey;
        end
      end

      // all commands are valid during this stage
      StCtrlOwnerIntKey: begin
        op_req = op_start_i;

        // when generating, select owner intermediate data input
        // when advancing, select owner as target
        // when disabling, select random data input
        stage_sel_o = disable_sel ? Disable  :
                      advance_sel ? Owner : OwnerInt;

        if (!en_i) begin
          state_d = StCtrlWipe;
        end else if (invalid_state) begin
          state_d = StCtrlDisabled;
        end else if (next_state) begin
          state_d = StCtrlOwnerKey;
        end
      end

      // all commands are valid during this stage
      // however advance goes directly to disabled state
      StCtrlOwnerKey: begin
        op_req = op_start_i;

        // when generating, select owner data input
        // when advancing, select disable as target
        // when disabling, select random data input
        stage_sel_o = disable_sel | advance_sel ? Disable : Owner;

        if (!en_i) begin
          state_d = StCtrlWipe;
        end else if (next_state || invalid_state) begin
          state_d = StCtrlDisabled;
        end
      end

      // The wipe state immediately clears out the key state, but waits for any ongoing
      // transaction to finish before going to disabled state.
      // Unlike the random state, this is an immedaite shutdown request, so all parts of the
      // key are wiped.
      StCtrlWipe: begin
        wipe_req = 1'b1;
        stage_sel_o = Disable;
        invalid_op = op_start_i;

        // If the enable is dropped during the middle of a transaction, we clear and wait for that
        // transaction to gracefully complete (if it can).
        // There are two scenarios:
        // 1. the operation completed right when we started wiping, in which case the done would
        //    clear the start.
        // 2. the operation completed before we started wiping, or there was never an operation to
        //    begin with (op_start_i == 0), in this case, don't wait and immediately transition
        if (!op_start_i) begin
          state_d = StCtrlInvalid;
        end
      end

      // Default state (StCtrlDisabled and StCtrlInvalid included)
      // Continue to kick off random transactions
      // All transactions are treated as invalid despite completing
      default: begin
        stage_sel_o = Disable;
        op_req = op_start_i;
        invalid_op = op_req;
        disabled = 1'b1;
      end
    endcase // unique case (state_q)
  end // always_comb

  // Current working state provided for software read
  // Certain states are collapsed for simplicity
  always_comb begin
    working_state_o = StInvalid;

    unique case (state_q)
      StCtrlReset, StCtrlEntropyReseed, StCtrlRandom, StCtrlRootKey:
        working_state_o = StReset;

      StCtrlInit:
        working_state_o = StInit;

      StCtrlCreatorRootKey:
        working_state_o = StCreatorRootKey;

      StCtrlOwnerIntKey:
        working_state_o = StOwnerIntKey;

      StCtrlOwnerKey:
        working_state_o = StOwnerKey;

      StCtrlDisabled:
        working_state_o = StDisabled;

      StCtrlWipe, StCtrlInvalid:
        working_state_o = StInvalid;

      default:
        working_state_o = StInvalid;
    endcase // unique case (state_q)
  end

  // if working over multiple CDIs, a fault of any
  // is considered an overall fault
  logic clr_err;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fault_err_q <= '0;
    end else if (op_update || op_ack) begin
      fault_err_q <= fault_err_d;
    end else if (fault_err_q && clr_err) begin
      fault_err_q <= '0;
    end
  end

  always_comb begin
    op_state_d = op_state_q;

    op_update = 1'b0;
    op_ack = 1'b0;
    op_update_sel = KeyUpdateIdle;

    random_ack = 1'b0;

    // output to kmac interface
    adv_en_o = 1'b0;
    id_en_o = 1'b0;
    gen_en_o = 1'b0;

    clr_err = 1'b0;

    unique case (op_state_q)
      StIdle: begin
        clr_err = 1'b1;

        if (random_req) begin
          op_state_d = StRandomize;
        end else if (adv_req) begin
          op_state_d = StAdv;
        end else if (id_req || gen_req) begin
          op_state_d = StWait;
        end
      end

      StRandomize: begin
        op_update_sel = KeyUpdateRandom;

        if (cnt < EntropyRounds-1) begin
          op_update = 1'b1;
        end
        // when mask population is complete, xor the root_key into the zero share
        // if in the future the root key is updated to 2 shares, it will direclty overwrite
        // the values here
        else begin
          random_ack = 1'b1;
          op_state_d  = StIdle;
        end
      end

      StAdv: begin
        adv_en_o = 1'b1;

        if (kmac_done_i && (cdi_cnt == CDIs-1)) begin
          op_ack = 1'b1;
          op_state_d = StIdle;
        end else if (kmac_done_i && (cdi_cnt < CDIs-1)) begin
          op_update = 1'b1;
          op_state_d = StAdvAck;
        end

        // Invalidate keys under the following conditions
        if (op_ack || op_update) begin
          op_update_sel = fault_err ? KeyUpdateWipe    :
                          disabled  ? KeyUpdateInvalid : KeyUpdateKmac;
        end
      end

      // drop adv_en_o to allow kmac interface handshake
      StAdvAck: begin
        op_state_d = StAdv;
      end

      // Not an advanced operation
      StWait: begin

        id_en_o = id_req;
        gen_en_o = gen_req;

        if (kmac_done_i) begin
          op_ack = 1'b1;
          op_state_d = StIdle;
        end

        if (op_ack) begin
          op_update_sel = fault_err ? KeyUpdateWipe :
                          disabled  ? KeyUpdateInvalid : KeyUpdateKmac;
        end
      end

      // What should go here?
      default:;

    endcase // unique case (adv_state_q)
  end


  // data errors are not relevant when operation was not accepted.
  // invalid operation errors can happen even when operations are not accepted.
  assign error_o[ErrInvalidOp]  = op_done_o & invalid_op;
  assign error_o[ErrInvalidCmd] = op_ack & fault_err;
  assign error_o[ErrInvalidIn]  = op_ack & kmac_input_invalid_i;
  assign error_o[ErrInvalidOut] = op_ack & ~kmac_out_valid;

  always_comb begin
    status_o = OpIdle;
    if (op_done_o) begin
      status_o = |error_o ? OpDoneFail : OpDoneSuccess;
    end else if (op_start_i) begin
      status_o = OpWip;
    end
  end


  ///////////////////////////////
  // Suppress kmac return data
  ///////////////////////////////
  // This is a separate data path from the FSM used to control the data_en_o output

  typedef enum logic [1:0] {
    StCtrlDataIdle,
    StCtrlDataEn,
    StCtrlDataDis,
    StCtrlDataWait
  } keymgr_ctrl_data_state_e;

  keymgr_ctrl_data_state_e data_st_d, data_st_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_st_q <= StCtrlDataIdle;
    end else begin
      data_st_q <= data_st_d;
    end
  end

  // The below control path is used for modulating the datapath to sideload and sw keys.
  // This path is separate from the data_valid_o path, thus creating two separate attack points.
  // The data is only enabled when a non-advance operation is invoked.
  // When an advance operation is called, the data is disabled. It will stay disabled until an
  // entire completion sequence is seen (op_done_o assert -> start_i de-assertion).
  // When a generate operation is called, the data is enabled.  However, any indication of this
  // supposedly being an advance call will force the path to disable again.
  always_comb begin
    data_st_d = data_st_q;
    data_en_o = 1'b0;
    unique case (data_st_q)

      StCtrlDataIdle: begin
        if (adv_en_o) begin
          data_st_d = StCtrlDataDis;
        end else if (id_en_o || gen_en_o) begin
          data_st_d = StCtrlDataEn;
        end
      end

      StCtrlDataEn: begin
        data_en_o = 1'b1;
        if (adv_en_o) begin
          data_st_d = StCtrlDataDis;
        end
      end

      StCtrlDataDis: begin
        if (op_done_o) begin
          data_st_d = StCtrlDataWait;
        end
      end

      StCtrlDataWait: begin
        if (!op_start_i) begin
          data_st_d = StCtrlDataIdle;
        end
      end

      default:;

    endcase // unique case (data_st_q)
  end




  ///////////////////////////////
  // Functions
  ///////////////////////////////

  // unclear what this is supposed to be yet
  // right now just check to see if it not all 0's and not all 1's
 function automatic logic valid_data_chk (logic [KeyWidth-1:0] value);

    return |value & ~&value;

  endfunction // byte_mask

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

  // stage select should always be Disable whenever it is not enabled
  `ASSERT(StageDisableSel_A, !en_i |-> stage_sel_o == Disable)

  // Unless it is a legal command, only select disable
  `ASSERT(InitLegalCommands_A, op_start_i & en_i & state_q inside {StCtrlInit} &
                               !(op_i inside {OpAdvance}) |-> stage_sel_o == Disable)

  // All commands are legal, so select disable only if operation is disable
  `ASSERT(GeneralLegalCommands_A, op_start_i & en_i &
                                  state_q inside {StCtrlCreatorRootKey, StCtrlOwnerIntKey} &
                                  (op_i inside {OpDisable}) |-> stage_sel_o == Disable)

  `ASSERT(OwnerLegalCommands_A, op_start_i & en_i & state_q inside {StCtrlOwnerKey} &
                                (op_i inside {OpAdvance, OpDisable}) |-> stage_sel_o == Disable)

  // load_key should not be high if there is no ongoing operation
  `ASSERT(LoadKey_A, key_o.valid |-> op_start_i)

  // The count value should always be 0 when a transaction start
  `ASSERT(CntZero_A, $rose(op_start_i) |-> cnt == '0)

endmodule
