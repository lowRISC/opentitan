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
  input sideload_sel_err_i,
  input sideload_fsm_err_i,

  // Software interface
  input op_start_i,
  input keymgr_ops_e op_i,
  input [CdiWidth-1:0] op_cdi_sel_i,
  output logic op_done_o,
  output keymgr_op_status_e status_o,
  output logic [ErrLastPos-1:0] error_o,
  output logic [FaultLastPos-1:0] fault_o,
  output logic data_hw_en_o,
  output logic data_sw_en_o,
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
  localparam int EccDataWidth = 64;
  localparam int EccWidth = 8;
  localparam int EccWords = KeyWidth / EccDataWidth;
  localparam int TotalEccWords = EccWords * Shares * CDIs;


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
  } state_e;
  state_e state_q, state_d;

  // A variable that represents differentiates states before root key and after root key.
  logic initialized;

  // There are two versions of the key state, one for sealing one for attestation
  // Among each version, there are multiple shares
  // Each share is a fixed multiple of the entropy width
  logic [CDIs-1:0][Shares-1:0][EntropyRounds-1:0][EntropyWidth-1:0] key_state_d;
  logic [CDIs-1:0][Shares-1:0][EccWords-1:0][EccDataWidth-1:0] key_state_ecc_words_d;
  logic [CDIs-1:0][Shares-1:0][EccWords-1:0][EccDataWidth-1:0] key_state_q;
  logic [CDIs-1:0][Shares-1:0][EccWords-1:0][EccWidth-1:0] key_state_ecc_q;
  logic [CntWidth-1:0] cnt;
  logic [CdiWidth-1:0] cdi_cnt;

  // error conditions
  logic invalid_kmac_out;
  logic invalid_op;
  logic cnt_err;
  // states fall out of sparsely encoded range
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

  // async errors have nothing to do with the operation and thus should not
  // impact operation results.
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
  logic ld_root_key;

  // wipe and initialize take precedence
  assign update_sel = wipe_req             ? KeyUpdateWipe   :
                      random_req           ? KeyUpdateRandom :
                      init_o | ld_root_key ? KeyUpdateRoot   : op_update_sel;

  ///////////////////////////
  //  interaction between main fsm and prng
  ///////////////////////////

  assign prng_en_o = random_req | disabled | invalid | wipe_req;

  //////////////////////////
  // Main Control FSM
  //////////////////////////
  // SEC_CM: CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StCtrlReset)

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


  //SEC_CM: CTRL.KEY.INTEGRITY
  assign key_state_ecc_words_d = key_state_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      key_state_q <= '0;
      key_state_ecc_q <= {TotalEccWords{prim_secded_pkg::SecdedInv7264ZeroEcc}};
    end else begin
      for (int i = 0; i < CDIs; i++) begin
        for (int j = 0; j < Shares; j++) begin
          for (int k = 0; k < EccWords; k++) begin
            {key_state_ecc_q[i][j][k], key_state_q[i][j][k]} <=
                prim_secded_pkg::prim_secded_inv_72_64_enc(key_state_ecc_words_d[i][j][k]);
          end
        end
      end
    end
  end

  logic [CDIs-1:0][Shares-1:0][EccWords-1:0] ecc_errs;
  for (genvar i = 0; i < CDIs; i++) begin : gen_ecc_loop_cdi
    for (genvar j = 0; j < Shares; j++) begin : gen_ecc_loop_shares
      for (genvar k = 0; k < EccWords; k++) begin : gen_ecc_loop_words
        logic [1:0] errs;
        prim_secded_inv_72_64_dec u_dec (
          .data_i({key_state_ecc_q[i][j][k], key_state_q[i][j][k]}),
          .data_o(),
          .syndrome_o(),
          .err_o(errs)
        );
        assign ecc_errs[i][j][k] = |errs;
      end
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
    .Width(CntWidth)
  ) u_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(op_ack | random_ack),
    .set_i('0),
    .set_cnt_i('0),
    .incr_en_i(op_update | random_req),
    .decr_en_i(1'b0),
    .step_i(CntWidth'(1'b1)),
    .cnt_o(cnt),
    .cnt_next_o(),
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

    // Most states are initialized, mark the exceptions
    initialized = 1'b1;

    // during certain states, the otp root key is continuosly loaded
    ld_root_key = 1'b0;

    // if state is ever faulted, hold on to this indication
    // until reset.
    state_intg_err_d = state_intg_err_q;

    unique case (state_q)
      // Only advance can be called from reset state
      StCtrlReset: begin
        initialized = 1'b0;

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
        initialized = 1'b0;
        prng_reseed_req_o = 1'b1;

        if (prng_reseed_ack_i) begin
          state_d = StCtrlRandom;
        end
      end

      // This state does not accept any command.
      StCtrlRandom: begin
        initialized = 1'b0;
        random_req = 1'b1;

        // when mask population is complete, xor the root_key into the zero share
        // if in the future the root key is updated to 2 shares, it will direclty overwrite
        // the values here
        if (int'(cnt) == EntropyRounds-1) begin
          random_ack = 1'b1;
          state_d = StCtrlRootKey;
        end
      end

      // load the root key.
      StCtrlRootKey: begin
        init_o = 1'b1;
        initialized = 1'b1;
        state_d = en_i ? StCtrlInit : StCtrlWipe;
      end

      // Beginning from the Init state, operations are accepted.
      // Only valid operation is advance state. If invalid command received,
      // random data is selected for operation and no persistent state is changed.
      StCtrlInit: begin
        op_req = op_start_i;

        // when advancing select creator data, otherwise use random input
        stage_sel_o = advance_sel ? Creator : Disable;
        invalid_op = op_start_i & ~(advance_sel | disable_sel);

        // as long as an operation is not requested, continously load root key
        // if it is valid.
        // If an invalidate condition hits, also stop loading key
        ld_root_key = ~op_start_i;
        if (!en_i || inv_state) begin
          state_d = StCtrlWipe;
          ld_root_key = '0;
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
  logic update_en;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      last_working_st <= StReset;
    end else if (update_en) begin
      last_working_st <= working_state_o;
    end
  end

  always_comb begin
    update_en = 1'b1;
    working_state_o = StInvalid;

    unique case (state_q)
      StCtrlReset, StCtrlEntropyReseed, StCtrlRandom:
        working_state_o = StReset;

      StCtrlRootKey, StCtrlInit:
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
        update_en = 1'b0;
        working_state_o = last_working_st;
      end

      StCtrlInvalid:
        working_state_o = StInvalid;

      default:
        working_state_o = StInvalid;
    endcase // unique case (state_q)
  end

  always_comb begin
    status_o = OpIdle;
    if (op_done_o) begin
      // It is possible for an operation to finish the same cycle en_i goes low.
      // The main fsm handling is one cycle behind, but still report operation
      // fail.
      status_o = |{error_o, fault_o} ? OpDoneFail : OpDoneSuccess;
    end else if (op_start_i) begin
      status_o = OpWip;
    end
  end


  /////////////////////////
  // Operateion state, handle advance and generate
  /////////////////////////

  logic op_fsm_err;
  keymgr_op_state_ctrl u_op_state (
    .clk_i,
    .rst_ni,
    .adv_req_i(adv_req),
    .dis_req_i(dis_req),
    .id_req_i(id_req),
    .gen_req_i(gen_req),
    .cnt_i(cdi_cnt),
    .op_ack_o(op_ack),
    .op_busy_o(op_busy),
    .op_update_o(op_update),
    .kmac_done_i,
    .adv_en_o,
    .id_en_o,
    .gen_en_o,
    .op_fsm_err_o(op_fsm_err)
  );

  // operational state cross check.  The state value must be consistent with
  // the input operations.
  logic op_state_cmd_err;
  assign op_state_cmd_err = (adv_en_o & ~(advance_sel | disable_sel)) |
                            (gen_en_o & ~gen_op);

  // operations fsm update precedence
  // when in invalid state, always update.
  // when in disabled state, always update unless a fault is encountered.
  assign op_update_sel = (op_ack | op_update) & invalid      ? KeyUpdateKmac :
                         (op_ack | op_update) & op_fault_err ? KeyUpdateWipe :
                         (op_ack | op_update) & disabled     ? KeyUpdateKmac :
                         (op_ack | op_update) & op_err       ? KeyUpdateIdle :
                         (op_ack | op_update)                ? KeyUpdateKmac : KeyUpdateIdle;


  ///////////////////////////////
  // Suppress kmac return data
  ///////////////////////////////

  logic data_fsm_err;
  keymgr_data_en_state u_data_en (
    .clk_i,
    .rst_ni,
    .hw_sel_i(hw_sel_o),
    .adv_en_i(adv_en_o),
    .id_en_i(id_en_o),
    .gen_en_i(gen_en_o),
    .op_done_i(op_done_o),
    .op_start_i,
    .data_hw_en_o,
    .data_sw_en_o,
    .fsm_err_o(data_fsm_err)
  );

  /////////////////////////
  // Cross-checks, errors and faults
  /////////////////////////

  logic vld_state_change_d, vld_state_change_q;
  assign vld_state_change_d = (state_d != state_q) &
                              (state_d inside {StCtrlRootKey,
                                               StCtrlCreatorRootKey,
                                               StCtrlOwnerIntKey,
                                               StCtrlOwnerKey});

  // capture for cross check in following cycle
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      vld_state_change_q <= '0;
    end else begin
      vld_state_change_q <= vld_state_change_d;
    end
  end

  // state cross check
  // if the state advanced, ensure that it was due to an advanced operation
  logic state_change_err;
  assign state_change_err = vld_state_change_q & !adv_op;

  keymgr_err u_err (
    .clk_i,
    .rst_ni,
    .invalid_op_i(invalid_op),
    .disabled_i(disabled | (initialized & ~en_i)),
    .invalid_i(invalid),
    .kmac_input_invalid_i,
    .shadowed_update_err_i,
    .kmac_op_err_i,
    .invalid_kmac_out_i(invalid_kmac_out),
    .sideload_sel_err_i,
    .kmac_cmd_err_i,
    .kmac_fsm_err_i,
    .kmac_done_err_i,
    .regfile_intg_err_i,
    .shadowed_storage_err_i,
    .ctrl_fsm_err_i(state_intg_err_q | state_intg_err_d),
    .data_fsm_err_i(data_fsm_err),
    .op_fsm_err_i(op_fsm_err),
    .ecc_err_i(|ecc_errs),
    .state_change_err_i(state_change_err),
    .op_state_cmd_err_i(op_state_cmd_err),
    .cnt_err_i(cnt_err),
    .reseed_cnt_err_i,
    .sideload_fsm_err_i,

    .op_update_i(op_update),
    .op_done_i(op_done_o),

    .sync_err_o(sync_err),
    .async_err_o(),
    .sync_fault_o(sync_fault),
    .async_fault_o(async_fault),
    .error_o,
    .fault_o
  );

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
  `ASSERT(DataEnDis_A, op_start_i & op_done_o |=> ~data_hw_en_o && ~data_sw_en_o)

  // Whenever data enable asserts, it must be the case that there was a generate or
  // id operation
  `ASSERT(DataEn_A, data_hw_en_o | data_sw_en_o |-> (id_en_o | gen_en_o) & ~adv_en_o)

  // Check that the FSM is linear and does not contain any loops
  `ASSERT_FPV_LINEAR_FSM(SecCmCFILinear_A, state_q, state_e)

endmodule
