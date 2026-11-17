// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module cheriot_mem_sys
  import cheriot_mem_sys_reg_pkg::*;
#(
  // TL-UL address type
  parameter type                  addr_t           = logic [top_pkg::TL_AW-1:0],
  // Top-level address map parameters
  parameter addr_t                MainSramBaseAddr = 'h1000_0000,
  parameter addr_t                MainSramTopAddr  = 'h1003_0000,
  parameter addr_t                NvmBaseAddr      = 'h3000_0000,
  parameter addr_t                NvmTopAddr       = 'h3020_0000,
  parameter addr_t                MetaSramBaseAddr = 'h1100_0000,
  parameter int unsigned          MemSizeRevbm     = 3072,
  // Run a second copy of the logic in lockstep with the main copy
  parameter bit                   SecLockstep      = 1'b1,
  // Cycles the second copy of the logic runs behind the main copy
  parameter int unsigned          LockstepOffset   = 1,
  parameter logic [NumAlerts-1:0] AlertAsyncOn     = {NumAlerts{1'b1}},
  parameter int unsigned          AlertSkewCycles  = 1
) (

  input  logic clk_i,
  input  logic rst_ni,

  // Scan mode, bypasses the reset of the second copy of the logic
  input  prim_mubi_pkg::mubi4_t scanmode_i,
  input  logic                  scan_rst_ni,

  // CHERIoT mode enabled
  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,

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
  logic tbre_done;
  logic core_alert_fatal_fault;
  logic lockstep_alert_fatal_fault;
  logic alert_test;


  //////////////
  // CSR Node //
  //////////////

  cheriot_mem_sys_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_d_i),
    .tl_o      (regs_tl_d_o),
    .reg2hw,
    .hw2reg,
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(reg_intg_err)
  );


  //////////
  // Core //
  //////////

  cheriot_mem_sys_core #(
    .addr_t          (addr_t),
    .MainSramBaseAddr(MainSramBaseAddr),
    .MainSramTopAddr (MainSramTopAddr),
    .NvmBaseAddr     (NvmBaseAddr),
    .NvmTopAddr      (NvmTopAddr),
    .MetaSramBaseAddr(MetaSramBaseAddr),
    .MemSizeRevbm    (MemSizeRevbm)
  ) u_cheriot_mem_sys_core (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tbre_base_addr_i   (reg2hw.tbre_base_addr),
    .tbre_num_caps_i    (reg2hw.tbre_num_caps),
    .tbre_start_i       (reg2hw.tbre_start),
    .tbre_regwen_o      (hw2reg.tbre_regwen),
    .tbre_status_o      (hw2reg.tbre_status),
    .tbre_epoch_o       (hw2reg.tbre_epoch),
    .tbre_done_o        (tbre_done),
    .alert_fatal_fault_o(core_alert_fatal_fault),
    .cored_tl_d_i,
    .cored_tag_h2d_i,
    .cored_tl_d_o,
    .cored_tag_d2h_o,
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
    cheriot_mem_sys_lockstep #(
      .LockstepOffset  (LockstepOffset),
      .addr_t          (addr_t),
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
      .cheriot_ena_i,
      .tbre_base_addr_i   (reg2hw.tbre_base_addr),
      .tbre_num_caps_i    (reg2hw.tbre_num_caps),
      .tbre_start_i       (reg2hw.tbre_start),
      .tbre_regwen_i      (hw2reg.tbre_regwen),
      .tbre_status_i      (hw2reg.tbre_status),
      .tbre_epoch_i       (hw2reg.tbre_epoch),
      .tbre_done_i        (tbre_done),
      .alert_fatal_fault_o(lockstep_alert_fatal_fault),
      .cored_tl_d_h2d_i   (cored_tl_d_i),
      .cored_tag_h2d_i,
      .cored_tl_d_d2h_i   (cored_tl_d_o),
      .cored_tag_d2h_i    (cored_tag_d2h_o),
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
  end else begin : gen_no_lockstep
    assign lockstep_alert_fatal_fault = 1'b0;

    // The scan inputs only bypass the reset of the second copy.
    logic unused_scan;
    assign unused_scan = ^{scanmode_i, scan_rst_ni};
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


  //////////////////
  // Alert Sender //
  //////////////////

  assign alert_test = reg2hw.alert_test.q & reg2hw.alert_test.qe;

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[0]),
    .SkewCycles(AlertSkewCycles),
    .IsFatal(1'b1)
  ) u_prim_alert_sender_fatal_fault (
    .clk_i,
    .rst_ni,
    .alert_test_i (alert_test),
    .alert_req_i  (reg_intg_err | core_alert_fatal_fault | lockstep_alert_fatal_fault),
    .alert_ack_o  (),
    .alert_state_o(),
    .alert_rx_i   (alert_rx_i[0]),
    .alert_tx_o   (alert_tx_o[0])
  );


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
  `ASSERT_KNOWN(IntrTbreDoneKnown_A, intr_tbre_done_o)

  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegsWeOnehotCheck_A,
      u_reg_regs, alert_tx_o[0])

  if (SecLockstep && LockstepOffset > 1) begin : gen_lockstep_rst_cnt_assert
    `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(LockstepResetCountAlertCheck_A,
        gen_lockstep.u_cheriot_mem_sys_lockstep.gen_reset_counter.u_rst_shadow_cnt, alert_tx_o[0])
  end

endmodule
