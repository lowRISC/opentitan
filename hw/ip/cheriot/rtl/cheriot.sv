// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"
`include "prim_fifo_assert.svh"

// SEC_CM: LOGIC.SHADOW
// TODO: Implement lockstep operation for this module

module cheriot
  import cheriot_reg_pkg::*;
#(
  // TL-UL address type
  parameter type   addr_t           = logic [top_pkg::TL_AW-1:0],
  // Top-level address map parameters
  parameter addr_t                MainSramBaseAddr = 'h1000_0000,
  parameter addr_t                MainSramTopAddr  = 'h1002_0000,
  parameter addr_t                NvmBaseAddr      = 'h2000_0000,
  parameter addr_t                NvmTopAddr       = 'h2020_0000,
  parameter addr_t                MetaSramBaseAddr = 'h0,
  parameter logic [NumAlerts-1:0] AlertAsyncOn     = {NumAlerts{1'b1}},
  parameter int unsigned          AlertSkewCycles  = 1
) (

  input  logic clk_i,
  input  logic rst_ni,

  // CHERIoT mode enabled
  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Device interface for CSRs
  input  tlul_pkg::tl_h2d_t regs_tl_d_i,
  output tlul_pkg::tl_d2h_t regs_tl_d_o,

  // Core data input port
  input  tlul_pkg::tl_h2d_t cored_tl_d_i,
  input  logic              cored_tag_h2d_i,
  output tlul_pkg::tl_d2h_t cored_tl_d_o,
  output logic              cored_tag_d2h_o,

  // TRVK revocation bitmap input port
  input  tlul_pkg::tl_h2d_t corerevbm_tl_i,
  output tlul_pkg::tl_d2h_t corerevbm_tl_o,

  // System revocation bitmap port
  input  tlul_pkg::tl_h2d_t revbm_tl_d_i,
  output tlul_pkg::tl_d2h_t revbm_tl_d_o,

  // Core data output port towards interconnect
  output tlul_pkg::tl_h2d_t cored_tl_h_o,
  input  tlul_pkg::tl_d2h_t cored_tl_h_i,

  // Meta SRAM host port (to external sram_ctrl)
  output tlul_pkg::tl_h2d_t meta_sram_tl_o,
  input  tlul_pkg::tl_d2h_t meta_sram_tl_i
);

  /////////////////
  // Address map //
  /////////////////

  // Revocation happens on 64-bit or 8-byte granularity.
  localparam int unsigned RevocationGranuleByte = 32'd8;
  // Number of heap bytes a single TL word in the meta store can track
  localparam int unsigned RevocationBytePerWord = top_pkg::TL_DW * RevocationGranuleByte;

  // A capability is 64 bit or 8 byte wide
  localparam int unsigned CapabilitySizeByte    = 32'd8;
  // Number of capability bytes a single TL word in the meta store can track
  localparam int unsigned CapabilityBytePerWord = top_pkg::TL_DW * CapabilitySizeByte;

  // Size of the TRVK revocation bitmap
  localparam addr_t RevBmSizeWord   = (MainSramTopAddr - MainSramBaseAddr) / RevocationBytePerWord;
  localparam addr_t RevBmSizeByte   = RevBmSizeWord * (top_pkg::TL_DW / 32'd8);
  // Size of the SRAM tag store
  localparam addr_t SramTagSizeWord = (MainSramTopAddr - MainSramBaseAddr) / CapabilityBytePerWord;
  localparam addr_t SramTagSizeByte = SramTagSizeWord * (top_pkg::TL_DW / 32'd8);
  // Size of the NVM tag store
  localparam addr_t NvmTagSizeWord  = (NvmTopAddr - NvmBaseAddr) / CapabilityBytePerWord;
  localparam addr_t NvmTagSizeByte  = NvmTagSizeWord * (top_pkg::TL_DW / 32'd8);

  // Address map
  localparam addr_t MetaRevBmBase       = MetaSramBaseAddr;
  localparam addr_t MetaNvmTagBase      = MetaRevBmBase       + RevBmSizeByte;
  localparam addr_t MetaMainSramTagBase = MetaNvmTagBase      + NvmTagSizeByte;
  localparam addr_t MetaTop             = MetaMainSramTagBase + SramTagSizeByte;

  typedef struct packed {
    logic csr_intg;
    logic tag_filter_fifo;
    logic meta_sram_intg;
    logic meta_sram_data_intg;
    logic rwm_error;
  } cheriot_fatal_error_t;

  /////////////
  // Signals //
  /////////////

  tlul_pkg::tl_h2d_t rmw_tl_h2d;
  logic              rmw_tag_h2d;
  logic [4:0]        rmw_bit_sel;
  tlul_pkg::tl_d2h_t rmw_tl_d2h;
  logic              rmw_tag_d2h;

  tlul_pkg::tl_h2d_t tags_tl_h2d;
  tlul_pkg::tl_d2h_t tags_tl_d2h;

  tlul_pkg::tl_h2d_t meta_mux_in_tl_h2d[32'd3];
  tlul_pkg::tl_d2h_t meta_mux_in_tl_d2h[32'd3];

  cheriot_regs_reg2hw_t reg2hw;

  logic alert_test;

  // Fatal errors
  cheriot_fatal_error_t cheriot_fatal_error;


  //////////////
  // CSR Node //
  //////////////

  cheriot_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_d_i),
    .tl_o      (regs_tl_d_o),
    .reg2hw,
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(cheriot_fatal_error.csr_intg)
  );


  ////////////
  // Filter //
  ////////////

  cheriot_access_check #(
    .addr_t(addr_t),
    .CheriotBaseAddr(MetaRevBmBase),
    .CheriotTopAddr(MetaNvmTagBase),
    .CheriotSubWordAllowed(1'b0)
  ) u_cheriot_access_check_trvk (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_h_i(corerevbm_tl_i),
    .tl_h_o(corerevbm_tl_o),
    .tl_d_o(meta_mux_in_tl_h2d[32'd0]),
    .tl_d_i(meta_mux_in_tl_d2h[32'd0])
  );

  cheriot_tag_filter #(
    .NumOutstanding(32'd2),
    .addr_t(addr_t),
    .MainSramBaseAddr(MainSramBaseAddr),
    .MainSramTopAddr(MainSramTopAddr),
    .NvmBaseAddr(NvmBaseAddr),
    .NvmTopAddr(NvmTopAddr),
    .MetaMainSramTagBase(MetaMainSramTagBase),
    .MetaNvmTagBase(MetaNvmTagBase)
  ) u_cheriot_tag_filter (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_d_i       (cored_tl_d_i),
    .tag_d_i      (cored_tag_h2d_i),
    .tl_d_o       (cored_tl_d_o),
    .tag_d_o      (cored_tag_d2h_o),
    .tl_m_o       (rmw_tl_h2d),
    .tag_m_o      (rmw_tag_h2d),
    .bit_sel_m_o  (rmw_bit_sel),
    .tl_m_i       (rmw_tl_d2h),
    .tag_m_i      (rmw_tag_d2h),
    .tl_h_o       (cored_tl_h_o),
    .tl_h_i       (cored_tl_h_i),
    .fifo_err_o   (cheriot_fatal_error.tag_filter_fifo)
  );

  // SEC_CM: BUS.INTEGRITY
  cheriot_rmw_filter #(
    .addr_t(addr_t)
  ) u_cheriot_rmw_filter (
    .clk_i,
    .rst_ni,
    .tl_h_i           (rmw_tl_h2d),
    .tag_h_i          (rmw_tag_h2d),
    .bit_sel_h_i      (rmw_bit_sel),
    .tl_h_o           (rmw_tl_d2h),
    .tag_h_o          (rmw_tag_d2h),
    .tl_d_o           (tags_tl_h2d),
    .tl_d_i           (tags_tl_d2h),
    .data_intg_error_o(cheriot_fatal_error.meta_sram_data_intg),
    .rsp_intg_error_o (cheriot_fatal_error.meta_sram_intg),
    .device_error_o   (cheriot_fatal_error.rwm_error)
  );

  cheriot_access_check #(
    .addr_t(addr_t),
    .CheriotBaseAddr(MetaNvmTagBase),
    .CheriotTopAddr(MetaTop),
    .CheriotSubWordAllowed(1'b0)
  ) u_cheriot_access_check_tags (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_h_i(tags_tl_h2d),
    .tl_h_o(tags_tl_d2h),
    .tl_d_o(meta_mux_in_tl_h2d[32'd1]),
    .tl_d_i(meta_mux_in_tl_d2h[32'd1])
  );

  cheriot_access_check #(
    .addr_t(addr_t),
    .CheriotBaseAddr(MetaRevBmBase),
    .CheriotTopAddr(MetaNvmTagBase),
    .CheriotSubWordAllowed(1'b0)
  ) u_cheriot_access_check_sys (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_h_i(revbm_tl_d_i),
    .tl_h_o(revbm_tl_d_o),
    .tl_d_o(meta_mux_in_tl_h2d[32'd2]),
    .tl_d_i(meta_mux_in_tl_d2h[32'd2])
  );


  ///////////////////////
  // Meta multiplexing //
  ///////////////////////

  tlul_socket_m1 #(
    .M(32'd3),
    .HReqDepth('0),
    .HRspDepth('0),
    .DReqDepth('0),
    .DRspDepth('0)
  ) u_tlul_socket_m1 (
    .clk_i,
    .rst_ni,
    .tl_h_i(meta_mux_in_tl_h2d),
    .tl_h_o(meta_mux_in_tl_d2h),
    .tl_d_o(meta_sram_tl_o),
    .tl_d_i(meta_sram_tl_i)
  );


  //////////////////
  // Alert Sender //
  //////////////////

  assign alert_test = reg2hw.alert_test.q & reg2hw.alert_test.qe;

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[0]),
    .SkewCycles(AlertSkewCycles),
    .IsFatal(1)
  ) u_prim_alert_sender_fatal_fault (
    .clk_i,
    .rst_ni,
    .alert_test_i  (alert_test),
    .alert_req_i   (|cheriot_fatal_error),
    .alert_ack_o   (),
    .alert_state_o (),
    .alert_rx_i    (alert_rx_i[0]),
    .alert_tx_o    (alert_tx_o[0])
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

  `ASSERT_KNOWN(MetaSramAValidKnown_A, meta_sram_tl_o.a_valid)
  `ASSERT_KNOWN(MetaSramDReadyKnown_A, meta_sram_tl_o.d_ready)
  `ASSERT_KNOWN_IF(MetaSramPayloadKnown_A, meta_sram_tl_o, meta_sram_tl_o.a_valid)

  `ASSERT_KNOWN(RegsTlDAReadyKnown_A, regs_tl_d_o.a_ready)
  `ASSERT_KNOWN(RegsTlDDValidKnown_A, regs_tl_d_o.d_valid)
  `ASSERT_KNOWN_IF(RegsTlDPayloadKnown_A, regs_tl_d_o, regs_tl_d_o.d_valid)

  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  `ASSERT_PRIM_FIFO_SYNC_ERROR_TRIGGERS_ALERT(CheriotTagFilterFifo_A,
      u_cheriot_tag_filter.u_prim_fifo_sync_align,
      alert_tx_o[0])

  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegsWeOnehotCheck_A,
      u_reg_regs, alert_tx_o[0])

endmodule
