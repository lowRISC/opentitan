// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager top level
//

`include "prim_assert.sv"

module keymgr_dpe_ctrl
  import keymgr_pkg::*;
  import keymgr_dpe_pkg::*;
  import keymgr_dpe_reg_pkg::*;
// TODO(#384): Bring back KmacEnMasking parameter
(
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
  input keymgr_dpe_ops_e op_i,
  input [DpeNumSlotsWidth-1:0] slot_src_sel_i,
  input [DpeNumSlotsWidth-1:0] slot_dst_sel_i,
  input [KeyVersionWidth-1:0] max_key_version_i,  // for the current stage

  output logic op_done_o,
  output keymgr_op_status_e status_o,
  output logic [ErrLastPos-1:0] error_o,
  output logic [FaultLastPos-1:0] fault_o,
  output logic data_hw_en_o,
  output logic data_sw_en_o,
  // `data_valid_o` gates:
  // (1) write requests to SW_OUTPUT key registers
  // (2) write requests to sideload ports
  output logic data_valid_o,
  output logic wipe_key_o,
  output keymgr_dpe_exposed_working_state_e working_state_o,
  output logic sw_binding_unlock_o,
  output logic init_o,

  // Data input
  input hw_key_req_t root_key_i,
  // `hw_sel_o == 1` indicates whether the generated key output
  // goes to sideload port. The safe default here is software CSR key.
  output prim_mubi_pkg::mubi4_t hw_sel_o,

  // KMAC ctrl interface
  output logic adv_en_o,
  output logic gen_en_o,
  output hw_key_req_t key_o,
  output keymgr_dpe_slot_t active_key_slot_o,

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

  keymgr_dpe_working_state_e state_q, state_d;
  // TODO(#384): Revisit SW-visible state mapping
  assign working_state_o = (state_q inside {StCtrlDpeReset, StCtrlDpeEntropyReseed,
                             StCtrlDpeRandom, StCtrlDpeRootKey}) ? StWorkDpeReset :
                           (state_q == StCtrlDpeAvailable) ? StWorkDpeAvailable :
                           (state_q inside {StCtrlDpeWipe, StCtrlDpeDisabled}) ? StWorkDpeDisabled :
                           StWorkDpeInvalid;

  logic [EntropyRndWidth-1:0] cnt;

  keymgr_dpe_slot_t [DpeNumSlots-1:0] key_slots_q;
  keymgr_dpe_slot_t [DpeNumSlots-1:0] key_slots_d;

  // error conditions
  logic invalid_kmac_out;
  logic cnt_err;
  // states fall out of sparsely encoded range
  logic state_intg_err_q, state_intg_err_d;

  // Shorthand variable to consider both HW key gen and SW key gen
  logic gen_key_op;
  assign gen_key_op = (op_i == OpDpeGenSwOut) | (op_i == OpDpeGenHwOut);

  ///////////////////////////
  //  interaction between software and main fsm
  ///////////////////////////
  logic advance_cmd;
  logic disable_cmd;
  logic gen_hw_key_cmd;

  assign advance_cmd    = op_start_i & (op_i == OpDpeAdvance)  & en_i;
  assign gen_hw_key_cmd = op_start_i & (op_i == OpDpeGenHwOut) & en_i;
  assign disable_cmd    = op_start_i & (op_i == OpDpeDisable)  & en_i;

  ///////////////////////////
  //  interaction between main control fsm and operation fsm
  ///////////////////////////

  // req/ack interface with op handling fsm
  logic op_req;
  logic op_ack;
  logic op_update;
  logic op_busy;
  logic disabled;

  logic adv_req, dis_req, gen_req, erase_req;
  assign adv_req   = op_req & (op_i == OpDpeAdvance);
  assign dis_req   = op_req & (op_i == OpDpeDisable);
  assign gen_req   = op_req & gen_key_op;
  assign erase_req = op_req & (op_i == OpDpeErase);

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
  // TODO(#384): fix invalidity check
  assign invalid_kmac_out = 0;

  // async errors have nothing to do with the operation and thus should not
  // impact operation results.
  assign op_err = |sync_err;

  assign op_fault_err = |{sync_fault, async_fault};

  ///////////////////////////
  //  key update controls
  ///////////////////////////

  // update select can come from both main and operation fsm's
  keymgr_dpe_key_update_e update_sel, op_update_sel;

  // req from main control fsm to key update controls
  logic wipe_req;
  logic random_req;
  logic random_ack;

  // wipe and initialize take precedence
  assign update_sel = wipe_req                       ? SlotQuickWipeAll   :
                      (state_q == StCtrlDpeRandom)   ? SlotDestRandomize  :
                      init_o                         ? SlotLoadRoot       : op_update_sel;

  // operations fsm update precedence
  // when in invalid state, always update.
  // when in disabled state, always update unless a fault is encountered.
  // op_update marks the clock cycle where KMAC returns the digest. It is the time to latch the key.
  assign op_update_sel = op_update & op_fault_err         ? SlotQuickWipeAll :
                         op_update & (op_err || disabled) ? SlotUpdateIdle   :
                         op_update & adv_req              ? SlotLoadFromKmac :
                         op_update & erase_req            ? SlotErase        : SlotUpdateIdle;

  ///////////////////////////
  //  interaction between main fsm and prng
  ///////////////////////////

  assign prng_en_o = random_req | disabled | wipe_req;

  //////////////////////////
  // Main Control FSM
  //////////////////////////

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

  // Check invalidity of the slot
  for (genvar i = 0; i < Shares; i++) begin : gen_key_out_assign
    assign key_o.key[i] = active_key_slot_o.valid ?
                          active_key_slot_o.key[i] :
                          {EntropyRounds{entropy_i[i]}};
  end

  // TODO(#384): Enable ECC so that we have key integrity
  //SEC_CM: CTRL.KEY.INTEGRITY
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // TODO(#384): Check writing '0 to policy bits is OK
      key_slots_q <= '0;
    end else begin
      key_slots_q <= key_slots_d;
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

  logic [DpeNumBootStagesWidth-1:0] active_slot_boot_stage;
  logic active_slot_valid;
  assign active_key_slot_o     = key_slots_q[slot_src_sel_i];
  assign active_slot_boot_stage = active_key_slot_o.boot_stage;
  assign active_slot_valid     = active_key_slot_o.valid;

  assign data_valid_o = op_ack & gen_key_op;
  assign wipe_key_o = update_sel == SlotQuickWipeAll;

  /////////////////////////
  // Keymgr slots MUX
  /////////////////////////

  always_comb begin
    key_slots_d = key_slots_q;

    unique case (update_sel)

      // `SlotDestRandomize` exists as a SCA counter-measure. It loads initial random bits into
      // keymgr slots, so that the sensitive secret values that loaded later are protected against
      // simple Hamming weight leakages.
      SlotDestRandomize: begin
        for (int j = 0; j < Shares; j++) begin
          key_slots_d[slot_dst_sel_i] = '0;
          // TODO(#384): Initialize pre-UDS value with equal randomness for SCA resistance
          // It should look like below:
          // key_slots_d[i].key[j][cnt*EntropyWidth +: EntropyWidth] = entropy_i[0];
        end
      end

      // `SlotLoadRoot` is used only once after reset, and it allows keymgr_DPE to store the root
      // secret (UDS) that comes from peripheral OTP port.
      SlotLoadRoot: begin
        key_slots_d[slot_dst_sel_i].valid = 1;
        key_slots_d[slot_dst_sel_i].boot_stage = 0;
        key_slots_d[slot_dst_sel_i].key[0] ^= root_key_i.key[0];
        key_slots_d[slot_dst_sel_i].key[1] ^= root_key_i.key[1];
        // TODO(#384): Revisit the default policy value for UDS latching
        // when further policy bits are added.
        key_slots_d[slot_dst_sel_i].key_policy.allow_child = 1;
      end

      // `SlotLoadFromKmac` is used at the end of a successful advance operation, so that the
      // digest computed by KMAC is stored in the specified keymgr slot as the key value of DPE.
      SlotLoadFromKmac: begin
        // Again the following check should go to FSM not this MUX!
        key_slots_d[slot_dst_sel_i].valid = 1;
        key_slots_d[slot_dst_sel_i].key = kmac_data_i;
        key_slots_d[slot_dst_sel_i].max_key_version = max_key_version_i;
        key_slots_d[slot_dst_sel_i].boot_stage = active_slot_boot_stage + 1;
        // TODO(#384): set policy
      end

      // `SlotErase` is used for erasing the slot selected by destination slot CSR. Erasing is a
      // regular SW invoked operation in keymgr_DPE, and it can serve two functions:
      // 1) Remove DPE contexts that should not be accessible in the later program flow
      // 2) Remove DPE contexts, so that the hardware keymgr slot can be used to derive another DPE
      // context through advance call.
      // This is different than `SlotQuickWipeAll`, which removes all secrets inside keymgr_DPE when
      // a fault is observed.
      SlotErase: begin
        for (int j = 0; j < Shares; j++) begin
          key_slots_d[slot_dst_sel_i] = '0;
          // TODO(#384): Instead of clearing with '0, use randomness.
          key_slots_d[slot_dst_sel_i].key[j][cnt*EntropyWidth+:EntropyWidth] = '0;
        end
      end

      // `SlotQuickWipeAll` is used in a panic/terminal state where keymgr_dpe won't be reused until
      // next reboot. This is triggered by detection of a fault attack.
      SlotQuickWipeAll: begin
        for (int i = 0; i < DpeNumSlots; i++) begin
          key_slots_d[i] = '0;
          for (int j = 0; j < Shares; j++) begin
            key_slots_d[i].key[j] = {EntropyRounds{entropy_i[j]}};
          end
        end
      end

      default:;
    endcase // unique case (update_sel)
  end

  // SEC_CM: CTRL.CTR.REDUN
  prim_count #(
    .Width(EntropyRndWidth)
  ) u_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(op_ack | random_ack),
    .set_i('0),
    .set_cnt_i('0),
    .incr_en_i(op_update | random_req),
    .decr_en_i(1'b0),
    .step_i(EntropyRndWidth'(1'b1)),
    .commit_i(1'b1),
    .cnt_o(cnt),
    .cnt_after_commit_o(),
    .err_o(cnt_err)
  );


  prim_mubi4_sender u_hw_sel (
    .clk_i,
    .rst_ni,
    .mubi_i (prim_mubi_pkg::mubi4_bool_to_mubi(gen_hw_key_cmd)),
    .mubi_o (hw_sel_o)
  );

  // op_req: up when both: 1) FSM is in a state to handle SW commands 2) the SW command comes
  // op_ack: comes back from the inner FSM (op_state) to confirm that the current operation is acked
  assign op_done_o = op_req ? op_ack : init_o;

  // SEC_CM: CTRL.FSM.LOCAL_ESC
  // begin invalidation when faults are observed.
  // sync faults only invalidate on transaction boudaries
  // async faults begin invalidating immediately

  // TODO(#384): Make sure that:
  // 1) inv_state is correctly computed
  // 2) inv_state is correctly consumed by FSM
  logic inv_state;
  assign inv_state = |fault_o;

  // SEC_CM: CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, keymgr_dpe_working_state_e, StCtrlDpeReset)

  // TODO(#384): This FSM currently lacks `invalid_op` signal that indicates that SW requested
  // operation is invalid (i.e. not permitted in given state). Hence, this needs to be defined and
  // FSM transitions need to be revisited.
  always_comb begin
    // persistent data
    state_d = state_q;

    // `op_req` is used to gate incoming SW requests from the actual computation logic (i.e. KMAC
    // invocation, slot updates etc). Hence, when `op_req = 0`, SW requests are only used for FSM
    // transitions. In other words, `op_req = 1` only when FSM reaches to the state to process
    // incoming requests.
    op_req = 1'b0;

    // lfsr interaction
    random_req = 1'b0;
    random_ack = 1'b0;

    // request to key updates
    wipe_req = 1'b0;

    // indication that state is disabled
    disabled = 1'b0;

    // enable prng toggling
    prng_reseed_req_o = 1'b0;

    // initialization complete
    init_o = 1'b0;

    // if state is ever faulted, hold on to this indication
    // until reset.
    state_intg_err_d = state_intg_err_q;

    unique case (state_q)
      // Only advance can be called from reset state
      StCtrlDpeReset: begin

        // if there was a structural fault before anything began, wipe immediately
        if (inv_state) begin
          state_d = StCtrlDpeWipe;
        end else if (advance_cmd) begin
          state_d = StCtrlDpeEntropyReseed;
        end
      end

      // reseed entropy
      StCtrlDpeEntropyReseed: begin
        prng_reseed_req_o = 1'b1;

        if (prng_reseed_ack_i) begin
          state_d = StCtrlDpeRandom;
        end
      end

      // `StCtrlDpeRandom` uses already seeded LFSRs to generate sufficient number of bits to fill
      // keymgr slots as SCA counter-measure (see `SlotDestRandomize` in slot MUX). When keymgr
      // slots are randomized, FSM moves the next state. Therefore, this state does not accept any
      // commands.
      StCtrlDpeRandom: begin
        random_req = 1'b1;

        if (int'(cnt) == EntropyRounds - 1) begin
          random_ack = 1'b1;
          state_d = StCtrlDpeRootKey;
        end
      end

      // load the root key.
      StCtrlDpeRootKey: begin
        init_o  = 1'b1;
        if (!en_i || inv_state) begin
          state_d = StCtrlDpeWipe;
        end else if (!root_key_valid_q) begin
          state_d = StCtrlDpeInvalid;
        end else begin
          state_d = StCtrlDpeAvailable;
        end
      end

      // In Available state, advance/generate/erase/disable operations are accepted.
      // Except for disable command or unexpected faults, FSM should linger on this state.
      StCtrlDpeAvailable: begin
        op_req = op_start_i;

        if (!en_i || inv_state) begin
          state_d = StCtrlDpeWipe;
        end else if (disable_cmd) begin
          state_d = StCtrlDpeDisabled;
        end
      end

      // TODO(#384): Revisit wiping behavior in the middle of ongoing transaction
      // In previous keymgr (not to be confused with this keymgr_dpe), the wipe state immediately
      // clears out the key state, but waits for any ongoing transaction to finish before going to
      // disabled state. For compatibility, we might want to do the same here, and let transaction
      // gracefully complete, even though its result will be void.
      StCtrlDpeWipe: begin
        wipe_req = 1'b1;

        state_d = StCtrlDpeInvalid;
      end

      // TODO(#384): Revisit allowing transactions during Disabled and Invalid.
      // In previous keymgr, in Disabled or Invalid states, SW can still request advance/generation
      // operations (even though technically that should not happen). This causes keymgr to issue
      // further KMAC transactions. Need to decide if we want to keep this behavior.
      StCtrlDpeDisabled: begin
        disabled = 1'b1;
        state_d = StCtrlDpeDisabled;
      end

      // Terminal state.
      StCtrlDpeInvalid: begin
        state_d = StCtrlDpeInvalid;
      end

      // latch the fault indication and start to wipe the key manager
      default: begin
        state_intg_err_d = 1'b1;
        state_d = StCtrlDpeWipe;
      end

    endcase // unique case (state_q)
  end // always_comb

  /////////////////////////
  // Last requested operation status
  /////////////////////////
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
  keymgr_dpe_op_state_ctrl u_op_state (
    .clk_i,
    .rst_ni,
    .adv_req_i(adv_req),
    .gen_req_i(gen_req),
    .erase_req_i(erase_req),
    .op_ack_o(op_ack),
    .op_busy_o(op_busy),
    .op_update_o(op_update),
    .kmac_done_i,
    .adv_en_o,
    .gen_en_o,
    .op_fsm_err_o(op_fsm_err)
  );

  ///////////////////////////////
  // Suppress kmac return data
  ///////////////////////////////

  logic data_fsm_err;
  keymgr_data_en_state u_data_en (
    .clk_i,
    .rst_ni,
    .hw_sel_i(hw_sel_o),
    .adv_en_i(adv_en_o),
    // Hardwire `id_en_i` to '0, because keymgr DPE does not identity generation
    .id_en_i(1'b0),
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


  // TODO(#384): Bring back counter-measure to check if state transitions are valid
  // and then remove these placeholder assignments
  assign sync_fault = '0;
  assign async_fault = '0;
  assign error_o = '0;
  assign fault_o = '0;
  assign sync_err = '0;

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

  // TODO(#384): Revisit assertions.
  // 1) Can these assertions be rewritten for keymgr_dpe context?
  // 2) Which of these should be removed because they are obsolete.
  // 3) Which new assertions should be added for keymgr_dpe?

  // This assertion will not work if fault_status ever takes on metafields such as
  // qe / re etc.
  `ASSERT_INIT(SameErrCnt_A, $bits(keymgr_dpe_reg2hw_fault_status_reg_t) ==
                             (SyncFaultLastIdx + AsyncFaultLastIdx))

  // // stage select should always be Disable whenever it is not enabled
  // `ASSERT(StageDisableSel_A, !en_i |-> stage_sel_o == Disable)

  // // Unless it is a legal command, only select disable
  // `ASSERT(
  //     InitLegalCommands_A,
  //     op_start_i & en_i & state_q inside {StCtrlInit} & !(op_i inside {OpDpeAdvance})
  //     |-> stage_sel_o == Disable)

  // // All commands are legal, so select disable only if operation is disable
  // `ASSERT(
  //     GeneralLegalCommands_A,
  //     op_start_i & en_i & state_q inside {StCtrlCreatorRootKey, StCtrlOwnerIntKey}
  //     & (op_i inside {OpDpeDisable})
  //     |-> stage_sel_o == Disable)

  // `ASSERT(
  //     OwnerLegalCommands_A,
  //     op_start_i & en_i & state_q inside {StCtrlOwnerKey} &
  //                                   (op_i inside {OpDpeAdvance, OpDpeDisable})
  //     |-> stage_sel_o == Disable)

  // load_key should not be high if there is no ongoing operation
  `ASSERT(LoadKey_A, key_o.valid |-> op_start_i)

  // The count value should always be 0 when a transaction start
  `ASSERT(CntZero_A, $rose(op_start_i) |-> cnt == '0)

  // Whenever a transaction completes, data_en must return to 0 on the next cycle
  `ASSERT(DataEnDis_A, op_start_i & op_done_o |=> ~data_hw_en_o && ~data_sw_en_o)

  // Whenever data enable asserts, it must be the case that there was a generate or
  // id operation
  `ASSERT(DataEn_A, data_hw_en_o | data_sw_en_o |-> gen_en_o & ~adv_en_o)

  // Check that the FSM is linear and does not contain any loops
  `ASSERT_FPV_LINEAR_FSM(SecCmCFILinear_A, state_q, keymgr_dpe_working_state_e)

endmodule
