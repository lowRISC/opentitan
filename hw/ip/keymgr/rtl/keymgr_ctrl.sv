// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager top level
//

`include "prim_assert.sv"

module keymgr_ctrl
  import keymgr_pkg::*;
  import keymgr_reg_pkg::*;
#(
  parameter bit KmacEnMasking = 1'b1
) (
  input clk_i,
  input rst_ni,

  // lifecycle enforcement
  // SEC_CM: CTRL.FSM.GLOBAL_ESC
  input en_i,

  // faults that can occur outside of operations
  input regfile_intg_err_i,
  input shadowed_update_err_i,
  input shadowed_storage_err_i,
  input reseed_cnt_err_i,
  input sideload_fsm_err_i,

  // Software interface
  input op_start_i,
  input keymgr_ops_e op_i,
  input [CdiWidth-1:0] op_cdi_sel_i,
  output logic op_done_o,
  output keymgr_op_status_e status_o,
  output logic [ErrLastPos-1:0] error_o,
  output logic [FaultLastPos-1:0] fault_o,
  output logic data_en_o,
  output logic data_valid_o,
  output logic wipe_key_o,
  output keymgr_working_state_e working_state_o,
  output logic sw_binding_unlock_o,
  output logic init_o,

  // Data input
  input  otp_ctrl_pkg::otp_keymgr_key_t root_key_i,
  output prim_mubi_pkg::mubi4_t hw_sel_o,
  output keymgr_stage_e stage_sel_o,
  output logic invalid_stage_sel_o,
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
  input kmac_done_err_i,// asserted when kmac unexpectedly toggles done
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
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 11 -n 10 \
  //      -s 4101887575 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (54.55%)
  //  6: |||||||||||||||| (45.45%)
  //  7: --
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StCtrlReset          = 10'b1101100001,
    StCtrlEntropyReseed  = 10'b1110010010,
    StCtrlRandom         = 10'b0011110100,
    StCtrlRootKey        = 10'b0110101111,
    StCtrlInit           = 10'b0100000100,
    StCtrlCreatorRootKey = 10'b1000011101,
    StCtrlOwnerIntKey    = 10'b0001001010,
    StCtrlOwnerKey       = 10'b1101111110,
    StCtrlDisabled       = 10'b1010101000,
    StCtrlWipe           = 10'b0000110011,
    StCtrlInvalid        = 10'b1011000111
  } keymgr_ctrl_state_e;

  keymgr_ctrl_state_e state_q, state_d;

  // There are two versions of the key state, one for sealing one for attestation
  // Among each version, there are multiple shares
  // Each share is a fixed multiple of the entropy width
  logic [CDIs-1:0][Shares-1:0][EntropyRounds-1:0][EntropyWidth-1:0] key_state_q, key_state_d;
  logic [CntWidth-1:0] cnt;
  logic [CdiWidth-1:0] cdi_cnt;

  // error conditions
  logic invalid_kmac_out;
  logic invalid_op;
  logic cnt_err;
  // states fall out of sparsely encoded range
  logic data_fsm_err;
  logic state_intg_err_q, state_intg_err_d;

  ///////////////////////////
  //  General operation decode
  ///////////////////////////

  logic adv_op, dis_op, gen_id_op, gen_sw_op, gen_hw_op, gen_op;
  assign adv_op    = (op_i == OpAdvance);
  assign gen_id_op = (op_i == OpGenId);
  assign gen_sw_op = (op_i == OpGenSwOut);
  assign gen_hw_op = (op_i == OpGenHwOut);
  assign dis_op    = ~(op_i inside {OpAdvance, OpGenId, OpGenSwOut, OpGenHwOut});
  assign gen_op    = (gen_id_op | gen_sw_op | gen_hw_op);

  ///////////////////////////
  //  interaction between software and main fsm
  ///////////////////////////
  // disable is treated like an advanced call
  logic advance_sel;
  logic disable_sel;
  logic gen_out_hw_sel;

  assign advance_sel    = op_start_i & adv_op    & en_i;
  assign gen_out_hw_sel = op_start_i & gen_hw_op & en_i;

  // disable is selected whenever a normal operation is not set
  assign disable_sel    = (op_start_i & dis_op) | !en_i;


  ///////////////////////////
  //  interaction between main control fsm and operation fsm
  ///////////////////////////

  // req/ack interface with op handling fsm
  logic op_req;
  logic op_ack;
  logic op_update;
  logic op_busy;
  logic disabled;
  logic invalid;

  logic adv_req, dis_req, id_req, gen_req;
  assign adv_req = op_req & adv_op;
  assign dis_req = op_req & dis_op;
  assign id_req  = op_req & gen_id_op;
  assign gen_req = op_req & (gen_sw_op | gen_hw_op);

  ///////////////////////////
  //  interaction between operation fsm and software
  ///////////////////////////
  // categories of keymgr errors
  logic [SyncErrLastIdx-1:0] sync_err;
  logic [AsyncErrLastIdx-1:0] async_err;
  logic [SyncFaultLastIdx-1:0] sync_fault;
  logic [AsyncFaultLastIdx-1:0] async_fault;

  logic op_err;
  logic op_fault_err;

  // unlock sw binding configuration whenever an advance call is made without errors
  assign sw_binding_unlock_o = adv_req & op_ack & ~(op_err | op_fault_err);

  // error definition
  // check incoming kmac data validity
  // Only check during the periods when there is actual kmac output
  assign invalid_kmac_out = (op_update | op_ack) &
                            (~valid_data_chk(kmac_data_i[0]) |
                            (~valid_data_chk(kmac_data_i[1]) & KmacEnMasking));

  assign op_err = |sync_err;

  assign op_fault_err = |{sync_fault, async_fault};


  ///////////////////////////
  //  key update controls
  ///////////////////////////

  // update select can come from both main and operation fsm's
  keymgr_key_update_e update_sel, op_update_sel;

  // req from main control fsm to key update controls
  logic wipe_req;
  logic random_req;
  logic random_ack;

  // wipe and initialize take precedence
  assign update_sel = wipe_req   ? KeyUpdateWipe   :
                      random_req ? KeyUpdateRandom :
                      init_o     ? KeyUpdateRoot   : op_update_sel;

  ///////////////////////////
  //  interaction between main fsm and prng
  ///////////////////////////

  assign prng_en_o = random_req | disabled | invalid | wipe_req;

  //////////////////////////
  // Main Control FSM
  //////////////////////////
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = keymgr_ctrl_state_e'(state_raw_q);
  // SEC_CM: CTRL.FSM.SPARSE
  prim_sparse_fsm_flop #(
    .StateEnumT(keymgr_ctrl_state_e),
    .Width(StateWidth),
    .ResetValue(StateWidth'(StCtrlReset))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( state_d     ),
    .state_o ( state_raw_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_intg_err_q <= '0;
    end else begin
      state_intg_err_q <= state_intg_err_d;
    end
  end

  // prevents unknowns from reaching the outside world.
  // - whatever operation causes the input data select to be disabled should not expose the key
  //   state.
  // - when there are no operations, the key state also should be exposed.
  assign key_o.valid = op_req;
  assign cdi_sel_o = advance_sel ? cdi_cnt : op_cdi_sel_i;

  assign invalid_stage_sel_o = ~(stage_sel_o inside {Creator, OwnerInt, Owner});
  for (genvar i = 0; i < Shares; i++) begin : gen_key_out_assign
    assign key_o.key[i] = invalid_stage_sel_o ?
                          {EntropyRounds{entropy_i[i]}} :
                          key_state_q[cdi_sel_o][i];
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      key_state_q <= '0;
    end else begin
      key_state_q <= key_state_d;
    end
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

  // Do not let the count toggle unless an advance operation is
  // selected
  assign cdi_cnt = op_req ? cnt[CdiWidth-1:0] : '0;

  always_comb begin
    key_state_d = key_state_q;
    data_valid_o = 1'b0;
    wipe_key_o = 1'b0;

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
            if (KmacEnMasking) begin : gen_two_share_key
              key_state_d[i][0] = root_key_i.key_share0;
              key_state_d[i][1] = root_key_i.key_share1;
            end else begin : gen_one_share_key
              key_state_d[i][0] = root_key_i.key_share0 ^ root_key_i.key_share1;
              key_state_d[i][1] = '0;
            end
          end
        end else begin
          // if root key is not valid, load and invalid value
          for (int i = 0; i < CDIs; i++) begin
              key_state_d[i][0] = '0;
              key_state_d[i][1] = '{default: '1};
          end
        end
      end

      KeyUpdateKmac: begin
        data_valid_o = gen_op;
        key_state_d[cdi_sel_o] = (adv_op || dis_op) ? kmac_data_i : key_state_q[cdi_sel_o];
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

  // SEC_CM: CTRL.CTR.REDUN
  prim_count #(
    .Width(CntWidth),
    .OutSelDnCnt(1'b0),
    .CntStyle(prim_count_pkg::DupCnt)
  ) u_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(op_ack | random_ack),
    .set_i('0),
    .set_cnt_i('0),
    .en_i(op_update | random_req),
    .step_i(CntWidth'(1'b1)),
    .cnt_o(cnt),
    .err_o(cnt_err)
  );


  prim_mubi4_sender u_hw_sel (
    .clk_i,
    .rst_ni,
    .mubi_i (prim_mubi_pkg::mubi4_bool_to_mubi(gen_out_hw_sel)),
    .mubi_o (hw_sel_o)
  );

  // when in a state that accepts commands, look at op_ack for completion
  // when in a state that does not accept commands, wait for other triggers.
  assign op_done_o = op_req ? op_ack :
                     (init_o | invalid_op);


  // There are 3 possibilities
  // advance to next state (software command)
  // advance to disabled state (software command)
  // advance to invalid state (detected fault)
  logic adv_state;
  logic dis_state;
  logic inv_state;
  assign adv_state = op_ack & adv_req & ~op_err;
  assign dis_state = op_ack & dis_req;

  // SEC_CM: CTRL.FSM.LOCAL_ESC
  // begin invalidation when faults are observed.
  // sync faults only invalidate on transaction boudaries
  // async faults begin invalidating immediately
  assign inv_state = |fault_o;

  always_comb begin
    // persistent data
    state_d = state_q;

    // request to op handling
    op_req = 1'b0;
    random_req = 1'b0;
    random_ack = 1'b0;

    // request to key updates
    wipe_req = 1'b0;

    // invalid operation issued
    invalid_op = '0;

    // data update and select signals
    stage_sel_o = Disable;

    // indication that state is disabled
    disabled = 1'b0;

    // indication that state is invalid
    invalid = 1'b0;

    // enable prng toggling
    prng_reseed_req_o = 1'b0;

    // initialization complete
    init_o = 1'b0;

    // if state is ever faulted, hold on to this indication
    // until reset.
    state_intg_err_d = state_intg_err_q;

    unique case (state_q)
      // Only advance can be called from reset state
      StCtrlReset: begin

        // always use random data for advance, since out of reset state
        // the key state will be randomized.
        stage_sel_o = Disable;

        // key state is updated when it is an advance call
        // all other operations are invalid, including disable
        invalid_op = op_start_i & ~advance_sel;

        // if there was a structural fault before anything began, wipe immediately
        if (inv_state) begin
          state_d = StCtrlWipe;
        end else if (advance_sel) begin
          state_d = StCtrlEntropyReseed;
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
        random_req = 1'b1;

        // when mask population is complete, xor the root_key into the zero share
        // if in the future the root key is updated to 2 shares, it will direclty overwrite
        // the values here
        if (cnt == EntropyRounds-1) begin
          random_ack = 1'b1;
          state_d = StCtrlRootKey;
        end
      end

      // load the root key.
      StCtrlRootKey: begin
        init_o = 1'b1;
        state_d = inv_state ? StCtrlWipe : StCtrlInit;
      end

      // Beginning from the Init state, operations are accepted.
      // Only valid operation is advance state. If invalid command received,
      // random data is selected for operation and no persistent state is changed.
      StCtrlInit: begin
        op_req = op_start_i;

        // when advancing select creator data, otherwise use random input
        stage_sel_o = advance_sel ? Creator : Disable;
        invalid_op = op_start_i & ~(advance_sel | disable_sel);

        if (!en_i || inv_state) begin
          state_d = StCtrlWipe;
        end else if (dis_state) begin
          state_d = StCtrlDisabled;
        end else if (adv_state) begin
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

        if (!en_i || inv_state) begin
          state_d = StCtrlWipe;
        end else if (dis_state) begin
          state_d = StCtrlDisabled;
        end else if (adv_state) begin
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

        if (!en_i || inv_state) begin
          state_d = StCtrlWipe;
        end else if (dis_state) begin
          state_d = StCtrlDisabled;
        end else if (adv_state) begin
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

        if (!en_i || inv_state) begin
          state_d = StCtrlWipe;
        end else if (adv_state || dis_state) begin
          state_d = StCtrlDisabled;
        end
      end

      // The wipe state immediately clears out the key state, but waits for any ongoing
      // transaction to finish before going to disabled state.
      // Unlike the random state, this is an immedaite shutdown request, so all parts of the
      // key are wiped.
      StCtrlWipe: begin
        wipe_req = 1'b1;
        // if there was already an operation ongoing, maintain the request until completion
        op_req = op_busy;
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

      // StCtrlDisabled and StCtrlInvalid are almost functionally equivalent
      // The only difference is that Disabled is entered through software invocation,
      // while Invalid is entered through life cycle disable or operational fault.
      //
      // Both states continue to kick off random transactions
      // All transactions are treated as invalid despite completing
      StCtrlDisabled: begin
        op_req = op_start_i;
        disabled = 1'b1;

        if (!en_i || inv_state) begin
          state_d = StCtrlWipe;
        end
      end

      StCtrlInvalid: begin
        op_req = op_start_i;
        invalid = 1'b1;
      end

      // latch the fault indication and start to wipe the key manager
      default: begin
        state_intg_err_d = 1'b1;
        state_d = StCtrlWipe;
      end

    endcase // unique case (state_q)
  end // always_comb

  // Current working state provided for software read
  // Certain states are collapsed for simplicity
  keymgr_working_state_e last_working_st;
  logic state_update;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      last_working_st <= StReset;
    end else if (state_update) begin
      last_working_st <= working_state_o;
    end
  end

  always_comb begin
    state_update = 1'b1;
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

      StCtrlWipe: begin
        state_update = 1'b0;
        working_state_o = last_working_st;
      end

      StCtrlInvalid:
        working_state_o = StInvalid;

      default:
        working_state_o = StInvalid;
    endcase // unique case (state_q)
  end


  /////////////////////////
  // Operateion state, handle advance and generate
  /////////////////////////


  localparam int OpStateWidth = 8;
  typedef enum logic [OpStateWidth-1:0] {
    StIdle   = 8'b10010101,
    StAdv    = 8'b00101000,
    StAdvAck = 8'b01000011,
    StWait   = 8'b11111110
  } keymgr_op_state_e;

  keymgr_op_state_e op_state_q, op_state_d;
  logic [OpStateWidth-1:0] op_state_raw_q;
  logic op_fsm_err;
  assign op_state_q = keymgr_op_state_e'(op_state_raw_q);
  prim_sparse_fsm_flop #(
    .StateEnumT(keymgr_op_state_e),
    .Width(OpStateWidth),
    .ResetValue(OpStateWidth'(StIdle))
  ) u_op_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( op_state_d     ),
    .state_o ( op_state_raw_q )
  );

  always_comb begin
    op_state_d = op_state_q;
    op_update = 1'b0;
    op_ack = 1'b0;
    op_busy = 1'b1;

    // output to kmac interface
    adv_en_o = 1'b0;
    id_en_o = 1'b0;
    gen_en_o = 1'b0;

    op_fsm_err = 1'b0;

    unique case (op_state_q)
      StIdle: begin
        op_busy = '0;
        if (adv_req || dis_req) begin
          op_state_d = StAdv;
        end else if (id_req || gen_req) begin
          op_state_d = StWait;
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
      end

      // drop adv_en_o to allow kmac interface handshake
      StAdvAck: begin
        op_state_d = StAdv;
      end

      // Not an advanced operation
      StWait: begin
        id_en_o = gen_id_op;
        gen_en_o = gen_sw_op | gen_hw_op;

        if (kmac_done_i) begin
          op_ack = 1'b1;
          op_state_d = StIdle;
        end
      end

      // error state
      default: begin
        // allow completion of transaction
        op_ack = 1'b1;
        op_fsm_err = 1'b1;
      end

    endcase // unique case (adv_state_q)
  end

  // operations fsm update precedence
  // when in invalid state, always update.
  // when in disabled state, always update unless a fault is encountered.
  assign op_update_sel = (op_ack | op_update) & invalid      ? KeyUpdateKmac :
                         (op_ack | op_update) & op_fault_err ? KeyUpdateWipe :
                         (op_ack | op_update) & disabled     ? KeyUpdateKmac :
                         (op_ack | op_update) & op_err       ? KeyUpdateIdle :
                         (op_ack | op_update)                ? KeyUpdateKmac : KeyUpdateIdle;


  // Advance calls are made up of multiple rounds of kmac operations.
  // Any sync error that occurs is treated as an error of the entire call.
  // Therefore sync errors that happen before the end of the call must be
  // latched.
  logic[SyncErrLastIdx-1:0] sync_err_q, sync_err_d;
  logic[SyncFaultLastIdx-1:0] sync_fault_q, sync_fault_d;

  logic err_vld;
  assign err_vld = op_update | op_done_o;

  // sync errors
  // When an operation encounters a fault, the operation is always rejected as the FSM
  // transitions to wipe.  When an operation is ongoing and en drops, it is also rejected.
  assign sync_err_d[SyncErrInvalidOp] = err_vld & (invalid_op | disabled | invalid | inv_state);
  assign sync_err_d[SyncErrInvalidIn] = err_vld & kmac_input_invalid_i;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sync_err_q <= '0;
    end else if (op_done_o) begin
      sync_err_q <= '0;
    end else if (op_update) begin
      sync_err_q <= sync_err_d;
    end
  end
  assign sync_err = sync_err_q | sync_err_d;

  // async errors
  assign async_err[AsyncErrShadowUpdate] = shadowed_update_err_i;

  // sync faults
  assign sync_fault_d[SyncFaultKmacOp] = err_vld & kmac_op_err_i;
  assign sync_fault_d[SyncFaultKmacOut] = err_vld & invalid_kmac_out;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sync_fault_q <= '0;
    end else if (op_done_o) begin
       sync_fault_q <= '0;
    end else if (op_update) begin
      sync_fault_q <= sync_fault_d;
    end
  end
  assign sync_fault = sync_fault_q | sync_fault_d;

  // async faults
  logic [AsyncFaultLastIdx-1:0] async_fault_q, async_fault_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      async_fault_q <= '0;
    end else begin
      async_fault_q <= async_fault;
    end
  end
  assign async_fault = async_fault_q | async_fault_d;
  assign async_fault_d[AsyncFaultKmacCmd]  = kmac_cmd_err_i;
  assign async_fault_d[AsyncFaultKmacFsm]  = kmac_fsm_err_i;
  assign async_fault_d[AsyncFaultKmacDone] = kmac_done_err_i;
  assign async_fault_d[AsyncFaultRegIntg]  = regfile_intg_err_i;
  assign async_fault_d[AsyncFaultShadow ]  = shadowed_storage_err_i;
  assign async_fault_d[AsyncFaultFsmIntg]  = state_intg_err_q | data_fsm_err | op_fsm_err;
  assign async_fault_d[AsyncFaultCntErr ]  = cnt_err;
  assign async_fault_d[AsyncFaultRCntErr]  = reseed_cnt_err_i;
  assign async_fault_d[AsyncFaultSideErr]  = sideload_fsm_err_i;

  // certain errors/faults can only happen when there's an actual kmac transaction,
  // others can happen with or without.
  // output to error code register
  assign error_o[ErrInvalidOp]    = op_done_o & sync_err[SyncErrInvalidOp];
  assign error_o[ErrInvalidIn]    = op_ack & sync_err[SyncErrInvalidIn];
  assign error_o[ErrShadowUpdate] = async_err[AsyncErrShadowUpdate];

  // output to fault code register
  assign fault_o[FaultKmacOp]    = op_ack & sync_fault[SyncFaultKmacOp];
  assign fault_o[FaultKmacOut]   = op_ack & sync_fault[SyncFaultKmacOut];
  assign fault_o[FaultKmacCmd]   = async_fault[AsyncFaultKmacCmd];
  assign fault_o[FaultKmacFsm]   = async_fault[AsyncFaultKmacFsm];
  assign fault_o[FaultKmacDone]  = async_fault[AsyncFaultKmacDone];
  assign fault_o[FaultRegIntg]   = async_fault[AsyncFaultRegIntg];
  assign fault_o[FaultShadow]    = async_fault[AsyncFaultShadow];
  assign fault_o[FaultCtrlFsm]   = async_fault[AsyncFaultFsmIntg];
  assign fault_o[FaultCtrlCnt]   = async_fault[AsyncFaultCntErr];
  assign fault_o[FaultReseedCnt] = async_fault[AsyncFaultRCntErr];
  assign fault_o[FaultSideFsm]   = async_fault[AsyncFaultSideErr];

  always_comb begin
    status_o = OpIdle;
    if (op_done_o) begin
      status_o = |{error_o, fault_o} ? OpDoneFail : OpDoneSuccess;
    end else if (op_start_i) begin
      status_o = OpWip;
    end
  end


  ///////////////////////////////
  // Suppress kmac return data
  ///////////////////////////////
  // This is a separate data path from the FSM used to control the data_en_o output
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (50.00%)
  //  6: |||||||||||||||| (40.00%)
  //  7: |||| (10.00%)
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 5
  // Maximum Hamming weight: 7
  //
  localparam int DataStateWidth = 10;
  typedef enum logic [DataStateWidth-1:0] {
    StCtrlDataIdle    = 10'b1001110111,
    StCtrlDataEn      = 10'b1110001011,
    StCtrlDataDis     = 10'b0110100110,
    StCtrlDataWait    = 10'b1010111000,
    StCtrlDataInvalid = 10'b1111010100
  } keymgr_ctrl_data_state_e;

  keymgr_ctrl_data_state_e data_st_d, data_st_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [DataStateWidth-1:0] data_st_raw_q;
  assign data_st_q = keymgr_ctrl_data_state_e'(data_st_raw_q);
  // SEC_CM: DATA.FSM.SPARSE
  prim_sparse_fsm_flop #(
    .StateEnumT(keymgr_ctrl_data_state_e),
    .Width(DataStateWidth),
    .ResetValue(DataStateWidth'(StCtrlDataIdle))
  ) u_data_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( data_st_d     ),
    .state_o ( data_st_raw_q )
  );

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
    data_fsm_err = 1'b0;
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
        if (op_done_o) begin
          data_st_d = StCtrlDataWait;
        end else if (adv_en_o) begin
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

      default: begin
        data_fsm_err = 1'b1;
      end


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

  // This assertion will not work if fault_status ever takes on metafields such as
  // qe / re etc.
  `ASSERT_INIT(SameErrCnt_A, $bits(keymgr_reg2hw_fault_status_reg_t) ==
                             (SyncFaultLastIdx + AsyncFaultLastIdx))

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

  // Whenever a transaction completes, data_en must return to 0 on the next cycle
  `ASSERT(DataEnDis_A, op_start_i & op_done_o |=> ~data_en_o)

  // Whenever data enable asserts, it must be the case that there was a generate or
  // id operation
  `ASSERT(DataEn_A, data_en_o |-> (id_en_o | gen_en_o) & ~adv_en_o)

endmodule
