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
  input  fsm_state_e     fsm_state_i,
  input  lc_tx_t         secrets_valid_i,
  // Local life cycle signal
  output lc_tx_t         lc_raw_test_rma_o,
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

  lc_tx_t lc_raw_test_rma;
  lc_tx_t lc_dft_en, lc_nvm_debug_en, lc_hw_debug_en, lc_cpu_en, lc_keymgr_en, lc_escalate_en;
  lc_tx_t lc_creator_seed_sw_rw_en, lc_owner_seed_sw_rw_en, lc_iso_part_sw_rd_en;
  lc_tx_t lc_iso_part_sw_wr_en, lc_seed_hw_rd_en;
  lc_keymgr_div_t lc_keymgr_div_d, lc_keymgr_div_q;

  always_comb begin : p_lc_signal_decode
    // Life cycle control signal defaults
    lc_raw_test_rma          = Off;
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
    // This ensures that once escalation has been triggered, it cannot go back to Off.
    lc_escalate_en           = lc_tx_or_hi(Off, lc_escalate_en_o);
    // Set to invalid diversification value by default.
    lc_keymgr_div_d          = RndCnstLcKeymgrDivInvalid;

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
            // Only enable life cycle TAP register for OTP test mechanisms.
            LcStRaw,
            LcStTestLocked0,
            LcStTestLocked1,
            LcStTestLocked2,
            LcStTestLocked3,
            LcStTestLocked4,
            LcStTestLocked5,
            LcStTestLocked6: begin
              lc_raw_test_rma = On;
            end
            ///////////////////////////////////////////////////////////////////
            // Enable DFT and debug functionality, including the CPU in the
            // test unlocked states.
            LcStTestUnlocked0,
            LcStTestUnlocked1,
            LcStTestUnlocked2,
            LcStTestUnlocked3,
            LcStTestUnlocked4,
            LcStTestUnlocked5,
            LcStTestUnlocked6: begin
              lc_raw_test_rma      = On;
              lc_dft_en            = On;
              lc_nvm_debug_en      = On;
              lc_hw_debug_en       = On;
              lc_cpu_en            = On;
              lc_iso_part_sw_wr_en = On;
              lc_keymgr_div_d      = RndCnstLcKeymgrDivTestDevRma;
            end
            ///////////////////////////////////////////////////////////////////
            // This is the last TEST_UNLOCKED state. The same feature set is enabled
            // as in the other TEST_UNLOCKED states above, except for NVM debug en,
            // which is disabled in this state.
            LcStTestUnlocked7: begin
              lc_raw_test_rma      = On;
              lc_dft_en            = On;
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
              // If secrets_valid_i is set to ON, we output OFF.
              // Note that we can convert ON to OFF with a bitwise inversion due to the encoding.
              lc_creator_seed_sw_rw_en = lc_tx_t'(~secrets_valid_i);
              // Only allow hardware to consume the seeds once personalized.
              // If secrets_valid_i is set to ON, we output ON.
              lc_seed_hw_rd_en = secrets_valid_i;
            end
            ///////////////////////////////////////////////////////////////////
            // Similar functions as PROD, with the following differences:
            // - hardware debug functionality (CPU TAP) is enabled,
            // - access to the isolated flash partition is disabled.
            LcStDev: begin
              lc_hw_debug_en         = On;
              lc_cpu_en              = On;
              lc_keymgr_en           = On;
              lc_owner_seed_sw_rw_en = On;
              lc_iso_part_sw_wr_en   = On;
              lc_keymgr_div_d        = RndCnstLcKeymgrDivTestDevRma;
              // Only allow provisioning if the device has not yet been personalized.
              // If secrets_valid_i is set to ON, we output OFF.
              // Note that we can convert ON to OFF with a bitwise inversion due to the encoding.
              lc_creator_seed_sw_rw_en = lc_tx_t'(~secrets_valid_i);
              // Only allow hardware to consume the seeds once personalized.
              // If secrets_valid_i is set to ON, we output ON.
              lc_seed_hw_rd_en = secrets_valid_i;
            end
            ///////////////////////////////////////////////////////////////////
            // Enable all test and production functions.
            LcStRma: begin
              lc_raw_test_rma          = On;
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
        end else begin
          lc_escalate_en = On;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Post-transition state. Behaves similarly to the virtual scrap
      // states below, with the exception that escalate_en is NOT asserted,
      // since that could trigger unwanted alerts / escalations and system resets.
      PostTransSt: ;
      ///////////////////////////////////////////////////////////////////
      // Virtual scrap states, make sure the escalation signal is
      // also asserted in this case.
      ScrapSt,
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

  prim_lc_sender u_prim_lc_sender_raw_test_rma (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_raw_test_rma),
    .lc_en_o(lc_raw_test_rma_o)
  );
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
  ) u_prim_flop_keymgr_div (
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
      lc_tx_test_false_strict(lc_raw_test_rma_o) &&
      lc_tx_test_false_strict(lc_dft_en_o) &&
      lc_tx_test_false_strict(lc_nvm_debug_en_o) &&
      lc_tx_test_false_strict(lc_hw_debug_en_o) &&
      lc_tx_test_false_strict(lc_cpu_en_o) &&
      lc_tx_test_false_strict(lc_creator_seed_sw_rw_en_o) &&
      lc_tx_test_false_strict(lc_owner_seed_sw_rw_en_o) &&
      lc_tx_test_false_strict(lc_iso_part_sw_rd_en_o) &&
      lc_tx_test_false_strict(lc_iso_part_sw_wr_en_o) &&
      lc_tx_test_false_strict(lc_seed_hw_rd_en_o) &&
      lc_tx_test_false_strict(lc_keymgr_en_o) &&
      lc_tx_test_false_strict(lc_dft_en_o) &&
      lc_keymgr_div_o == RndCnstLcKeymgrDivInvalid)


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
                            TokenCheck1St,
                            PostTransSt})
      |=>
      lc_tx_test_true_strict(lc_escalate_en_o))

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
                           LcStTestUnlocked1,
                           LcStTestUnlocked2,
                           LcStTestUnlocked3,
                           LcStTestUnlocked4,
                           LcStTestUnlocked5,
                           LcStTestUnlocked6,
                           LcStTestUnlocked7,
                           LcStTestLocked0,
                           LcStTestLocked1,
                           LcStTestLocked2,
                           LcStTestLocked3,
                           LcStTestLocked4,
                           LcStTestLocked5,
                           LcStTestLocked6,
                           LcStDev,
                           LcStProd,
                           LcStProdEnd,
                           LcStRma})
      |=>
      lc_tx_test_true_strict(lc_escalate_en_o))

endmodule : lc_ctrl_signal_decode
