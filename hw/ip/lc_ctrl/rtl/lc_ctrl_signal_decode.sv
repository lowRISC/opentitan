// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle signal decoder and sender module.

module lc_ctrl_signal_decode
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
#(
  // Random netlist constants
  // SCRAP, RAW, TEST_LOCKED*, INVALID
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivInvalid    = LcKeymgrDivWidth'(0),
  // TEST_UNLOCKED*, DEV, RMA
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivTestDevRma = LcKeymgrDivWidth'(1),
  // PROD, PROD_END
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivProduction = LcKeymgrDivWidth'(2)
  ) (
  input                  clk_i,
  input                  rst_ni,
  // Life cycle state vector.
  input  logic           lc_state_valid_i,
  input  lc_state_e      lc_state_i,
  input  lc_id_state_e   lc_id_state_i,
  input  fsm_state_e     fsm_state_i,
  // Escalation enable from escalation receiver.
  input                  esc_wipe_secrets_i,
  // Life cycle broadcast outputs.
  output lc_tx_t         lc_dft_en_o,
  output lc_tx_t         lc_nvm_debug_en_o,
  output lc_tx_t         lc_hw_debug_en_o,
  output lc_tx_t         lc_cpu_en_o,
  output lc_tx_t         lc_creator_seed_sw_rw_en_o,
  output lc_tx_t         lc_owner_seed_sw_rw_en_o,
  output lc_tx_t         lc_iso_part_sw_rd_en_o,
  output lc_tx_t         lc_iso_part_sw_wr_en_o,
  output lc_tx_t         lc_seed_hw_rd_en_o,
  output lc_tx_t         lc_keymgr_en_o,
  output lc_tx_t         lc_escalate_en_o,
  // State group diversification value for keymgr
  output lc_keymgr_div_t lc_keymgr_div_o
);

  //////////////////////////
  // Signal Decoder Logic //
  //////////////////////////

  lc_tx_t lc_dft_en, lc_nvm_debug_en, lc_hw_debug_en, lc_cpu_en, lc_keymgr_en, lc_escalate_en;
  lc_tx_t lc_creator_seed_sw_rw_en, lc_owner_seed_sw_rw_en, lc_iso_part_sw_rd_en;
  lc_tx_t lc_iso_part_sw_wr_en, lc_seed_hw_rd_en;
  lc_keymgr_div_t lc_keymgr_div_d, lc_keymgr_div_q;

  always_comb begin : p_lc_signal_decode
    // Life cycle control signal defaults
    lc_dft_en                = Off;
    lc_nvm_debug_en          = Off;
    lc_hw_debug_en           = Off;
    lc_cpu_en                = Off;
    lc_creator_seed_sw_rw_en = Off;
    lc_owner_seed_sw_rw_en   = Off;
    lc_iso_part_sw_rd_en     = Off;
    lc_iso_part_sw_wr_en     = Off;
    lc_seed_hw_rd_en         = Off;
    lc_keymgr_en             = Off;
    lc_escalate_en           = Off;
    // Set to invalid diversification value by default.
    lc_keymgr_div_d          = RndCnstLcKeymgrDivInvalid;
    // The escalation life cycle signal is always decoded, no matter
    // which state we currently are in.
    // Note that this can be overridden by scrap states further below.
    if (esc_wipe_secrets_i) begin
      lc_escalate_en = On;
    end

    unique case (fsm_state_i)
      ///////////////////////////////////////////////////////////////////
      // Don't broadcast anything in this state.
      ResetSt: ;
      ///////////////////////////////////////////////////////////////////
      // Broadcasting of most signals is only enabled during the following life cycle states.
      IdleSt,
      ClkMuxSt,
      CntIncrSt,
      CntProgSt,
      TransCheckSt,
      FlashRmaSt,
      TokenHashSt,
      TokenCheck0St,
      TokenCheck1St,
      TransProgSt: begin
        if (lc_state_valid_i) begin
          unique case (lc_state_i)
            ///////////////////////////////////////////////////////////////////
            // RAW and test locked states, nothing to broadcast
            LcStRaw,
            LcStTestLocked0,
            LcStTestLocked1,
            LcStTestLocked2: ;
            ///////////////////////////////////////////////////////////////////
            // Enable DFT and debug functionality, including the CPU in the
            // test unlocked states.
            LcStTestUnlocked0,
            LcStTestUnlocked1,
            LcStTestUnlocked2,
            LcStTestUnlocked3: begin
              lc_dft_en            = On;
              lc_nvm_debug_en      = On;
              lc_hw_debug_en       = On;
              lc_cpu_en            = On;
              lc_iso_part_sw_wr_en = On;
              lc_keymgr_div_d      = RndCnstLcKeymgrDivTestDevRma;
            end
            ///////////////////////////////////////////////////////////////////
            // Enable production functions
            LcStProd,
            LcStProdEnd: begin
              lc_cpu_en              = On;
              lc_keymgr_en           = On;
              lc_owner_seed_sw_rw_en = On;
              lc_iso_part_sw_wr_en   = On;
              lc_iso_part_sw_rd_en   = On;
              lc_keymgr_div_d        = RndCnstLcKeymgrDivProduction;
              // Only allow provisioning if the device has not yet been personalized.
              if (lc_id_state_i == LcIdBlank) begin
                lc_creator_seed_sw_rw_en = On;
              end
              // Only allow hardware to consume the seeds once personalized.
              if (lc_id_state_i == LcIdPersonalized) begin
                lc_seed_hw_rd_en = On;
              end

            end
            ///////////////////////////////////////////////////////////////////
            // Same functions as PROD, but with additional debug functionality.
            LcStDev: begin
              lc_hw_debug_en         = On;
              lc_cpu_en              = On;
              lc_keymgr_en           = On;
              lc_owner_seed_sw_rw_en = On;
              lc_iso_part_sw_wr_en   = On;
              lc_iso_part_sw_rd_en   = On;
              lc_keymgr_div_d        = RndCnstLcKeymgrDivTestDevRma;
              // Only allow provisioning if the device has not yet been personalized.
              if (lc_id_state_i == LcIdBlank) begin
                lc_creator_seed_sw_rw_en = On;
              end
              // Only allow hardware to consume the seeds once personalized.
              if (lc_id_state_i == LcIdPersonalized) begin
                lc_seed_hw_rd_en = On;
              end
            end
            ///////////////////////////////////////////////////////////////////
            // Enable all test and production functions.
            LcStRma: begin
              lc_dft_en                = On;
              lc_nvm_debug_en          = On;
              lc_hw_debug_en           = On;
              lc_cpu_en                = On;
              lc_keymgr_en             = On;
              lc_creator_seed_sw_rw_en = On;
              lc_owner_seed_sw_rw_en   = On;
              lc_iso_part_sw_wr_en     = On;
              lc_iso_part_sw_rd_en     = On;
              lc_seed_hw_rd_en         = On;
              lc_keymgr_div_d          = RndCnstLcKeymgrDivTestDevRma;
            end
            ///////////////////////////////////////////////////////////////////
            // Invalid or scrapped life cycle state, make sure the escalation
            // signal is also asserted in this case.
            default: begin
              lc_escalate_en = On;
            end
          endcase // lc_state_i
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Virtual scrap states, make sure the escalation signal is
      // also asserted in this case.
      PostTransSt,
      EscalateSt,
      InvalidSt: begin
        lc_escalate_en = On;
      end
      default: begin
        lc_escalate_en = On;
      end
    endcase // fsm_state_i
  end

  /////////////////////////////////
  // Control signal output flops //
  /////////////////////////////////

  prim_lc_sender u_prim_lc_sender_dft_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_dft_en),
    .lc_en_o(lc_dft_en_o)
  );
  prim_lc_sender u_prim_lc_sender_nvm_debug_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_nvm_debug_en),
    .lc_en_o(lc_nvm_debug_en_o)
  );
  prim_lc_sender u_prim_lc_sender_hw_debug_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_hw_debug_en),
    .lc_en_o(lc_hw_debug_en_o)
  );
  prim_lc_sender u_prim_lc_sender_cpu_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_cpu_en),
    .lc_en_o(lc_cpu_en_o)
  );
  prim_lc_sender u_prim_lc_sender_creator_seed_sw_rw_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_creator_seed_sw_rw_en),
    .lc_en_o(lc_creator_seed_sw_rw_en_o)
  );
  prim_lc_sender u_prim_lc_sender_owner_seed_sw_rw_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_owner_seed_sw_rw_en),
    .lc_en_o(lc_owner_seed_sw_rw_en_o)
  );
  prim_lc_sender u_prim_lc_sender_iso_part_sw_rd_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_iso_part_sw_rd_en),
    .lc_en_o(lc_iso_part_sw_rd_en_o)
  );
  prim_lc_sender u_prim_lc_sender_iso_part_sw_wr_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_iso_part_sw_wr_en),
    .lc_en_o(lc_iso_part_sw_wr_en_o)
  );
  prim_lc_sender u_prim_lc_sender_seed_hw_rd_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_seed_hw_rd_en),
    .lc_en_o(lc_seed_hw_rd_en_o)
  );
  prim_lc_sender u_prim_lc_sender_keymgr_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_keymgr_en),
    .lc_en_o(lc_keymgr_en_o)
  );
  prim_lc_sender u_prim_lc_sender_escalate_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_escalate_en),
    .lc_en_o(lc_escalate_en_o)
  );

  assign lc_keymgr_div_o = lc_keymgr_div_q;

  prim_flop #(
    .Width(LcKeymgrDivWidth),
    .ResetValue(RndCnstLcKeymgrDivInvalid)
  ) u_prim_flo_keymgr_div (
    .clk_i  ( clk_i           ),
    .rst_ni ( rst_ni          ),
    .d_i    ( lc_keymgr_div_d ),
    .q_o    ( lc_keymgr_div_q )
  );

  ////////////////
  // Assertions //
  ////////////////

  // Need to make sure that the random netlist constants
  // are unique.
  `ASSERT_INIT(LcKeymgrDivUnique0_A,
      !(RndCnstLcKeymgrDivInvalid inside {RndCnstLcKeymgrDivTestDevRma,
                                          RndCnstLcKeymgrDivProduction}))
  `ASSERT_INIT(LcKeymgrDivUnique1_A, RndCnstLcKeymgrDivProduction != RndCnstLcKeymgrDivTestDevRma)

  `ASSERT(SignalsAreOffWhenNotEnabled_A,
      !lc_state_valid_i
      |=>
      lc_dft_en_o == Off &&
      lc_nvm_debug_en_o == Off &&
      lc_hw_debug_en_o == Off &&
      lc_cpu_en_o == Off &&
      lc_creator_seed_sw_rw_en_o == Off &&
      lc_owner_seed_sw_rw_en_o == Off &&
      lc_iso_part_sw_rd_en_o == Off &&
      lc_iso_part_sw_wr_en_o == Off &&
      lc_seed_hw_rd_en_o == Off &&
      lc_keymgr_en_o == Off &&
      lc_dft_en_o == Off &&
      lc_keymgr_div_o == RndCnstLcKeymgrDivInvalid)

  `ASSERT(EscalationAlwaysDecoded_A,
      esc_wipe_secrets_i |=> lc_escalate_en_o == On)

  `ASSERT(FsmInScrap_A,
      !(fsm_state_i inside {ResetSt,
                            TransProgSt,
                            IdleSt,
                            ClkMuxSt,
                            CntIncrSt,
                            CntProgSt,
                            TransCheckSt,
                            FlashRmaSt,
                            TokenHashSt,
                            TokenCheck0St,
                            TokenCheck1St})
      |=>
      lc_escalate_en_o == On)

  `ASSERT(StateInScrap_A,
      lc_state_valid_i &&
      fsm_state_i inside {IdleSt,
                          ClkMuxSt,
                          CntIncrSt,
                          CntProgSt,
                          TransCheckSt,
                          FlashRmaSt,
                          TokenHashSt,
                          TokenCheck0St,
                          TokenCheck1St} &&
      !(lc_state_i inside {LcStRaw,
                           LcStTestUnlocked0,
                           LcStTestLocked0,
                           LcStTestUnlocked1,
                           LcStTestLocked1,
                           LcStTestUnlocked2,
                           LcStTestLocked2,
                           LcStTestUnlocked3,
                           LcStDev,
                           LcStProd,
                           LcStProdEnd,
                           LcStRma})
      |=>
      lc_escalate_en_o == On)

endmodule : lc_ctrl_signal_decode
