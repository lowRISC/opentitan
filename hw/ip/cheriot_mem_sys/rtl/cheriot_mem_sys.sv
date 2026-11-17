// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module cheriot_mem_sys
  import cheriot_mem_sys_reg_pkg::*;
#(
  // Top-level address map parameters
  parameter logic [top_pkg::TL_AW-1:0] MainSramBaseAddr = 'h1000_0000,
  parameter logic [top_pkg::TL_AW-1:0] MainSramTopAddr  = 'h1003_0000,
  parameter logic [top_pkg::TL_AW-1:0] NvmBaseAddr      = 'h3000_0000,
  parameter logic [top_pkg::TL_AW-1:0] NvmTopAddr       = 'h3020_0000,
  parameter logic [top_pkg::TL_AW-1:0] MetaSramBaseAddr = 'h1100_0000,
  parameter int unsigned               MemSizeRevbm     = 3072,
  // Run a second copy of the logic in lockstep with the main copy
  parameter bit                        SecLockstep      = 1'b1,
  // Cycles the second copy of the logic runs behind the main copy
  parameter int unsigned               LockstepOffset   = 1,
  parameter logic [NumAlerts-1:0]      AlertAsyncOn     = {NumAlerts{1'b1}},
  parameter int unsigned               AlertSkewCycles  = 1
) (

  input  logic clk_i,
  input  logic rst_ni,
  input  logic rst_shadowed_ni,

  // Scan mode, bypasses the reset of the second copy of the logic
  input  prim_mubi_pkg::mubi4_t scanmode_i,
  input  logic                  scan_rst_ni,

  // CHERIoT mode enables: the main copy's, the second copy's (raised one cycle later) and the one
  // that turns on their comparison
  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,
  input  prim_mubi_pkg::mubi4_t cheriot_ena_shadow_i,
  input  prim_mubi_pkg::mubi4_t cheriot_ena_cmp_i,

  // Interrupts
  output logic intr_tbre_done_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Device interface for CSRs
  input  tlul_pkg::tl_h2d_t regs_tl_d_i,
  output tlul_pkg::tl_d2h_t regs_tl_d_o,

  // Core data input port
  input  tlul_pkg::tl_h2d_t     cored_tl_d_i,
  input  prim_mubi_pkg::mubi4_t cored_tag_h2d_i,
  output tlul_pkg::tl_d2h_t     cored_tl_d_o,
  output prim_mubi_pkg::mubi4_t cored_tag_d2h_o,

  // TRVK revocation bitmap input port
  input  tlul_pkg::tl_h2d_t corerevbm_tl_i,
  output tlul_pkg::tl_d2h_t corerevbm_tl_o,

  // System revocation bitmap port
  input  tlul_pkg::tl_h2d_t revbm_tl_d_i,
  output tlul_pkg::tl_d2h_t revbm_tl_d_o,

  // Core data output port towards interconnect
  output tlul_pkg::tl_h2d_t cored_tl_h_o,
  input  tlul_pkg::tl_d2h_t cored_tl_h_i,

  // Revocation engine read-only port towards interconnect
  output tlul_pkg::tl_h2d_t tbre_tl_h_o,
  input  tlul_pkg::tl_d2h_t tbre_tl_h_i,

  // Meta SRAM host port (to external sram_ctrl)
  output tlul_pkg::tl_h2d_t meta_sram_tl_o,
  input  tlul_pkg::tl_d2h_t meta_sram_tl_i
);

  /////////////
  // Signals //
  /////////////

  cheriot_mem_sys_regs_reg2hw_t reg2hw;
  cheriot_mem_sys_regs_hw2reg_t hw2reg;

  logic reg_intg_err;
  logic shadowed_storage_err;
  logic shadowed_update_err;
  logic tbre_done;
  logic core_alert_fatal_fault;
  logic lockstep_alert_fatal_fault;
  logic cheriot_ena_mismatch;

  logic [NumAlerts-1:0] alert;
  logic [NumAlerts-1:0] alert_test;


  //////////////
  // CSR Node //
  //////////////

  // SEC_CM: TBRE.CONFIG.SHADOW
  cheriot_mem_sys_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
    .tl_i                  (regs_tl_d_i),
    .tl_o                  (regs_tl_d_o),
    .reg2hw,
    .hw2reg,
    .shadowed_storage_err_o(shadowed_storage_err),
    .shadowed_update_err_o (shadowed_update_err),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o            (reg_intg_err)
  );

  assign hw2reg.recov_err_code.d                     = 1'b1;
  assign hw2reg.recov_err_code.de                    = shadowed_update_err;
  assign hw2reg.fatal_err_code.reg_intg.d            = 1'b1;
  assign hw2reg.fatal_err_code.reg_intg.de           = reg_intg_err;
  assign hw2reg.fatal_err_code.shadow_storage_err.d  = 1'b1;
  assign hw2reg.fatal_err_code.shadow_storage_err.de = shadowed_storage_err;


  /////////////////////////
  // CHERIoT Mode Enable //
  /////////////////////////

  // Receiver of the main copy's enable, one buffered copy for the main copy and one for the enable
  // comparison. With AsyncOn(0) the primitive only buffers.
  typedef enum logic [1:0] {
    EnaCoreIdx,
    EnaCompareIdx,
    EnaLast
  } cheriot_ena_pos_e;

  prim_mubi_pkg::mubi4_t [EnaLast-1:0] cheriot_ena;

  prim_mubi4_sync #(
    .NumCopies(int'(EnaLast)),
    .AsyncOn  (1'b0)
  ) u_cheriot_ena_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(cheriot_ena_i),
    .mubi_o(cheriot_ena)
  );


  /////////////////////
  // Capability tags //
  /////////////////////

  // SEC_CM: CORED_TAG.INTERSIG.MUBI
  // The request tag and the main copy's response tag get one buffered copy each for the main copy
  // or the port and one for the lockstep, so synthesis cannot share logic between the two. With
  // AsyncOn(0) the receivers add no flop.
  typedef enum logic [1:0] {
    TagMainIdx,
    TagLockstepIdx,
    TagLast
  } cored_tag_pos_e;

  prim_mubi_pkg::mubi4_t [TagLast-1:0] cored_tag_h2d_buf, cored_tag_d2h_buf;
  prim_mubi_pkg::mubi4_t               core_cored_tag_d2h;

  prim_mubi4_sync #(
    .NumCopies(int'(TagLast)),
    .AsyncOn  (1'b0)
  ) u_cored_tag_h2d_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(cored_tag_h2d_i),
    .mubi_o(cored_tag_h2d_buf)
  );

  prim_mubi4_sync #(
    .NumCopies(int'(TagLast)),
    .AsyncOn  (1'b0)
  ) u_cored_tag_d2h_sync (
    .clk_i,
    .rst_ni,
    .mubi_i(core_cored_tag_d2h),
    .mubi_o(cored_tag_d2h_buf)
  );

  assign cored_tag_d2h_o = cored_tag_d2h_buf[TagMainIdx];


  //////////
  // Core //
  //////////

  cheriot_mem_sys_core #(
    .MainSramBaseAddr(MainSramBaseAddr),
    .MainSramTopAddr (MainSramTopAddr),
    .NvmBaseAddr     (NvmBaseAddr),
    .NvmTopAddr      (NvmTopAddr),
    .MetaSramBaseAddr(MetaSramBaseAddr),
    .MemSizeRevbm    (MemSizeRevbm)
  ) u_cheriot_mem_sys_core (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i      (cheriot_ena[EnaCoreIdx]),
    .tbre_base_addr_i   (reg2hw.tbre_base_addr_shadowed),
    .tbre_num_caps_i    (reg2hw.tbre_num_caps_shadowed),
    .tbre_start_i       (reg2hw.tbre_start),
    .tbre_regwen_o      (hw2reg.tbre_regwen),
    .tbre_status_o      (hw2reg.tbre_status),
    .tbre_epoch_o       (hw2reg.tbre_epoch),
    .tbre_done_o        (tbre_done),
    .alert_fatal_fault_o(core_alert_fatal_fault),
    .cored_tl_d_i,
    .cored_tag_h2d_i    (cored_tag_h2d_buf[TagMainIdx]),
    .cored_tl_d_o,
    .cored_tag_d2h_o    (core_cored_tag_d2h),
    .corerevbm_tl_i,
    .corerevbm_tl_o,
    .revbm_tl_d_i,
    .revbm_tl_d_o,
    .cored_tl_h_o,
    .cored_tl_h_i,
    .tbre_tl_h_o,
    .tbre_tl_h_i,
    .meta_sram_tl_o,
    .meta_sram_tl_i
  );


  //////////////
  // Lockstep //
  //////////////

  // SEC_CM: LOGIC.SHADOW
  if (SecLockstep) begin : gen_lockstep
    prim_mubi_pkg::mubi4_t cheriot_ena_shadow;

    cheriot_mem_sys_lockstep #(
      .LockstepOffset  (LockstepOffset),
      .MainSramBaseAddr(MainSramBaseAddr),
      .MainSramTopAddr (MainSramTopAddr),
      .NvmBaseAddr     (NvmBaseAddr),
      .NvmTopAddr      (NvmTopAddr),
      .MetaSramBaseAddr(MetaSramBaseAddr),
      .MemSizeRevbm    (MemSizeRevbm)
    ) u_cheriot_mem_sys_lockstep (
      .clk_i,
      .rst_ni,
      .scanmode_i,
      .scan_rst_ni,
      .cheriot_ena_shadow_i,
      .cheriot_ena_shadow_o(cheriot_ena_shadow),
      .tbre_base_addr_i   (reg2hw.tbre_base_addr_shadowed),
      .tbre_num_caps_i    (reg2hw.tbre_num_caps_shadowed),
      .tbre_start_i       (reg2hw.tbre_start),
      .tbre_regwen_i      (hw2reg.tbre_regwen),
      .tbre_status_i      (hw2reg.tbre_status),
      .tbre_epoch_i       (hw2reg.tbre_epoch),
      .tbre_done_i        (tbre_done),
      .alert_fatal_fault_o(lockstep_alert_fatal_fault),
      .cored_tl_d_h2d_i   (cored_tl_d_i),
      .cored_tag_h2d_i    (cored_tag_h2d_buf[TagLockstepIdx]),
      .cored_tl_d_d2h_i   (cored_tl_d_o),
      .cored_tag_d2h_i    (cored_tag_d2h_buf[TagLockstepIdx]),
      .corerevbm_tl_h2d_i (corerevbm_tl_i),
      .corerevbm_tl_d2h_i (corerevbm_tl_o),
      .revbm_tl_d_h2d_i   (revbm_tl_d_i),
      .revbm_tl_d_d2h_i   (revbm_tl_d_o),
      .cored_tl_h_h2d_i   (cored_tl_h_o),
      .cored_tl_h_d2h_i   (cored_tl_h_i),
      .tbre_tl_h_h2d_i    (tbre_tl_h_o),
      .tbre_tl_h_d2h_i    (tbre_tl_h_i),
      .meta_sram_tl_h2d_i (meta_sram_tl_o),
      .meta_sram_tl_d2h_i (meta_sram_tl_i)
    );

    // Receiver of the compare enable
    prim_mubi_pkg::mubi4_t [0:0] cheriot_ena_cmp;

    prim_mubi4_sync #(
      .NumCopies(1),
      .AsyncOn  (1'b0)
    ) u_cheriot_ena_cmp_sync (
      .clk_i,
      .rst_ni,
      .mubi_i(cheriot_ena_cmp_i),
      .mubi_o(cheriot_ena_cmp)
    );

    // SEC_CM: CHERIOT_ENABLE.CTRL.REDUN, INTERSIG.MUBI
    // Any compare enable other than MuBi4False turns the comparison on, so a corrupted compare
    // enable keeps comparing. It passes the same LockstepOffset - 1 flops as the second copy's
    // enable, so it turns the comparison on only after that enable has settled, and it must turn
    // off at least LockstepOffset - 1 cycles before cheriot_ena_i changes.
    prim_mubi_pkg::mubi4_t cheriot_ena_cmp_delayed;

    // The mode switch in rv_core_ibex turns the compare enable off two cycles before
    // cheriot_ena_i changes.
    `ASSERT_INIT(LockstepOffsetMax_A, LockstepOffset <= 3)
    `ASSERT_STATIC_LINT_ERROR(LockstepOffsetMax_L, LockstepOffset <= 3)

    if (LockstepOffset > 1) begin : gen_cheriot_ena_cmp_delay
      // Stage LockstepOffset - 1 is the input, stage 0 feeds the comparison.
      logic [LockstepOffset-1:0][prim_mubi_pkg::MuBi4Width-1:0] cheriot_ena_cmp_q;

      assign cheriot_ena_cmp_q[LockstepOffset-1] = cheriot_ena_cmp[0];

      for (genvar i = 0; i < LockstepOffset - 1; i++) begin : gen_stages
        prim_flop #(
          .Width     (prim_mubi_pkg::MuBi4Width),
          .ResetValue(prim_mubi_pkg::MuBi4False)
        ) u_prim_cheriot_ena_cmp_flop (
          .clk_i,
          .rst_ni,
          .d_i(cheriot_ena_cmp_q[i+1]),
          .q_o(cheriot_ena_cmp_q[i])
        );
      end

      assign cheriot_ena_cmp_delayed = prim_mubi_pkg::mubi4_t'(cheriot_ena_cmp_q[0]);
    end else begin : gen_no_cheriot_ena_cmp_delay
      assign cheriot_ena_cmp_delayed = cheriot_ena_cmp[0];
    end

    assign cheriot_ena_mismatch =
        !prim_mubi_pkg::mubi4_test_false_strict(cheriot_ena_cmp_delayed) &&
        (prim_mubi_pkg::mubi4_test_invalid(cheriot_ena[EnaCompareIdx]) ||
         prim_mubi_pkg::mubi4_test_invalid(cheriot_ena_shadow) ||
         (cheriot_ena[EnaCompareIdx] != cheriot_ena_shadow));
  end else begin : gen_no_lockstep
    assign lockstep_alert_fatal_fault = 1'b0;
    assign cheriot_ena_mismatch       = 1'b0;

    // The scan inputs only bypass the reset of the second copy; the second copy's enable, the
    // compare enable and the tag copies for the lockstep only serve the second copy.
    logic unused_lockstep_inputs;
    assign unused_lockstep_inputs = ^{scanmode_i, scan_rst_ni, cheriot_ena[EnaCompareIdx],
                                      cheriot_ena_shadow_i, cheriot_ena_cmp_i,
                                      cored_tag_h2d_buf[TagLockstepIdx],
                                      cored_tag_d2h_buf[TagLockstepIdx]};
  end


  ///////////////
  // Interrupt //
  ///////////////

  prim_intr_hw #(
    .Width(1)
  ) u_intr_tbre_done (
    .clk_i,
    .rst_ni,
    .event_intr_i          (tbre_done),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.d),
    .intr_o                (intr_tbre_done_o)
  );


  ///////////////////
  // Alert Senders //
  ///////////////////

  assign alert[AlertFatalFaultIdx]         = reg_intg_err | shadowed_storage_err |
                                             core_alert_fatal_fault | lockstep_alert_fatal_fault |
                                             cheriot_ena_mismatch;
  assign alert[AlertRecovCtrlUpdateErrIdx] = shadowed_update_err;

  assign alert_test[AlertFatalFaultIdx]         = reg2hw.alert_test.fatal_fault.q &
                                                  reg2hw.alert_test.fatal_fault.qe;
  assign alert_test[AlertRecovCtrlUpdateErrIdx] = reg2hw.alert_test.recov_ctrl_update_err.q &
                                                  reg2hw.alert_test.recov_ctrl_update_err.qe;

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .SkewCycles(AlertSkewCycles),
      .IsFatal(i == AlertFatalFaultIdx)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i (alert_test[i]),
      .alert_req_i  (alert[i]),
      .alert_ack_o  (),
      .alert_state_o(),
      .alert_rx_i   (alert_rx_i[i]),
      .alert_tx_o   (alert_tx_o[i])
    );
  end


  ////////////////
  // Assertions //
  ////////////////

  // Device ports: handshake signals are always known, the payload only while it is valid.
  `ASSERT_KNOWN(CoredTlDAReadyKnown_A, cored_tl_d_o.a_ready)
  `ASSERT_KNOWN(CoredTlDDValidKnown_A, cored_tl_d_o.d_valid)
  `ASSERT_KNOWN_IF(CoredTlDPayloadKnown_A, cored_tl_d_o, cored_tl_d_o.d_valid)
  `ASSERT_KNOWN(CoredTagD2hKnown_A, cored_tag_d2h_o)

  `ASSERT_KNOWN(CoreRevBmAReadyKnown_A, corerevbm_tl_o.a_ready)
  `ASSERT_KNOWN(CoreRevBmDValidKnown_A, corerevbm_tl_o.d_valid)
  `ASSERT_KNOWN_IF(CoreRevBmPayloadKnown_A, corerevbm_tl_o, corerevbm_tl_o.d_valid)

  `ASSERT_KNOWN(RevBmTlDAReadyKnown_A, revbm_tl_d_o.a_ready)
  `ASSERT_KNOWN(RevBmTlDDValidKnown_A, revbm_tl_d_o.d_valid)
  `ASSERT_KNOWN_IF(RevBmTlDPayloadKnown_A, revbm_tl_d_o, revbm_tl_d_o.d_valid)

  // Host ports: handshake signals are always known, the payload only while the request is valid.
  `ASSERT_KNOWN(CoredTlHAValidKnown_A, cored_tl_h_o.a_valid)
  `ASSERT_KNOWN(CoredTlHDReadyKnown_A, cored_tl_h_o.d_ready)
  `ASSERT_KNOWN_IF(CoredTlHPayloadKnown_A, cored_tl_h_o, cored_tl_h_o.a_valid)

  `ASSERT_KNOWN(TbreTlHAValidKnown_A, tbre_tl_h_o.a_valid)
  `ASSERT_KNOWN(TbreTlHDReadyKnown_A, tbre_tl_h_o.d_ready)
  `ASSERT_KNOWN_IF(TbreTlHPayloadKnown_A, tbre_tl_h_o, tbre_tl_h_o.a_valid)

  `ASSERT_KNOWN(MetaSramAValidKnown_A, meta_sram_tl_o.a_valid)
  `ASSERT_KNOWN(MetaSramDReadyKnown_A, meta_sram_tl_o.d_ready)
  `ASSERT_KNOWN_IF(MetaSramPayloadKnown_A, meta_sram_tl_o, meta_sram_tl_o.a_valid)

  `ASSERT_KNOWN(RegsTlDAReadyKnown_A, regs_tl_d_o.a_ready)
  `ASSERT_KNOWN(RegsTlDDValidKnown_A, regs_tl_d_o.d_valid)
  `ASSERT_KNOWN_IF(RegsTlDPayloadKnown_A, regs_tl_d_o, regs_tl_d_o.d_valid)

  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)
  `ASSERT_KNOWN(LockstepAlertKnown_A, lockstep_alert_fatal_fault)
  `ASSERT_KNOWN(CheriotEnaKnown_A, cheriot_ena_i)
  `ASSERT_KNOWN(CheriotEnaShadowKnown_A, cheriot_ena_shadow_i)
  `ASSERT_KNOWN(CheriotEnaCmpKnown_A, cheriot_ena_cmp_i)
  `ASSERT_KNOWN(IntrTbreDoneKnown_A, intr_tbre_done_o)

  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegsWeOnehotCheck_A,
      u_reg_regs, alert_tx_o[AlertFatalFaultIdx])

  if (SecLockstep && LockstepOffset > 1) begin : gen_lockstep_rst_cnt_assert
    `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(LockstepResetCountAlertCheck_A,
        gen_lockstep.u_cheriot_mem_sys_lockstep.gen_reset_counter.u_rst_shadow_cnt,
        alert_tx_o[AlertFatalFaultIdx])
  end

endmodule
