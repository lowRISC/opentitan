// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I3C top level wrapper for OpenTitan.
//
// - OpenTitan compatibility, register interface and alert handling.
// - TileLink Uncached Light (TL-UL) interface.

`include "prim_assert.sv"

module i3c
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
#(
  parameter int unsigned            ClkFreq          = 50_000_000,
  parameter logic   [NumAlerts-1:0] AlertAsyncOn     = '1,
  // Number of cycles of differential skew tolerated on the alert signal.
  parameter int unsigned            AlertSkewCycles  = 1,
  // Number of target(s) or target group(s) presented simultaneously on the I3C bus,
  // including the Secondary Controller Role.
  parameter int unsigned            NumTargets       = i3c_pkg::NumTargets,
  parameter int unsigned            NumSDALanes      = 1,
  // Whether to include direct software access to the message buffer?
  parameter bit                     SWDirectMsgBuf   = 1'b1,
  // Whether the direct message buffer access supports execution.
  parameter prim_mubi_pkg::mubi4_t  SWDirEnIFetch    = prim_mubi_pkg::MuBi4False,
  // Hardware Identification Extended Capability.
  parameter int unsigned            CompManufacturer = i3c_pkg::CompManufacturer,
  parameter int unsigned            CompVersion      = i3c_pkg::CompVersion,
  parameter int unsigned            CompType         = i3c_pkg::CompType,
  // Register Access Control List.
  parameter bit                     EnableRacl      = 1'b0,
  parameter bit                     RaclErrorRsp    = EnableRacl,
  parameter top_racl_pkg::racl_policy_sel_t RaclPolicySelVec[NumRegs] = '{NumRegs{0}}
) (
  // IP block clock and reset.
  input                                     clk_i,
  input                                     rst_ni,

  // Always ON domain clock and reset.
  input                                     clk_aon_i,
  input                                     rst_aon_ni,

  // Register interface
  input  tlul_pkg::tl_h2d_t                 tl_i,
  output tlul_pkg::tl_d2h_t                 tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t    racl_policies_i,
  output top_racl_pkg::racl_error_log_t     racl_error_o,

  // I3C Controller I/O signaling.
  output i3c_io_pkg::i3c_ctrl_bus_drv_t     cio_ctrl_bus_drv_o,
  input  i3c_io_pkg::i3c_ctrl_bus_obv_t     cio_ctrl_bus_obv_i,

  // Pull-up enables for open drain intervals.
  output logic                              cio_ctrl_scl_pu_en_o,
  output logic                              cio_ctrl_sda_pu_en_o,

  // High-keeper enables.
  output logic                              cio_scl_hk_en_o,
  output logic                              cio_sda_hk_en_o,

  // I3C Target I/O signaling.
  output i3c_io_pkg::i3c_targ_bus_drv_t     cio_targ_bus_drv_o,
  input  i3c_io_pkg::i3c_targ_bus_obv_t     cio_targ_bus_obv_i,

  // Target Reset Detector request/response.
  output                                    rstdet_enable_o,
  output i3c_rstdet_req_t                   rstdet_req_o,
  input  i3c_rstdet_rsp_t                   rstdet_rsp_i,

  // Interrupts.
  // - HCI-global interrupt, asserted when any HCI interrupt is asserted.
  output logic                              intr_hci_o,
  // -  Target-global interrupt.
  output logic                              intr_targ_o,

  // DFT-related controls.
  input  prim_ram_1p_pkg::ram_1p_cfg_t      ram_cfg_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t  ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_t      dat_cfg_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t  dat_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_t      dct_cfg_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t  dct_cfg_rsp_o,
  input                                     mbist_en_i,
  input                                     scan_clk_i,
  input                                     scan_rst_ni,
  input prim_mubi_pkg::mubi4_t              scanmode_i

  // TODO: Dummy ports for top-level integration in the presence of topgen.
  ,
  output cio_ctrl_scl_en_o,
  output cio_ctrl_sda_en_o,
  output cio_targ_sda_en_o
);

  localparam int unsigned DataWidth = top_pkg::TL_DW;

  // Width of buffer address, in bits.
  localparam int unsigned BufAddrW = i3c_pkg::BufAddrW;

  // Device Address Table parameters.
  localparam int unsigned DATAddrW = $clog2(NumDATEntries);
  // Device Characteristics Table parameters.
  localparam int unsigned DCTAddrW = $clog2(NumDCTEntries);

  // Width of SW Direct Message Buffer address, in bits.
  localparam int unsigned SWDirAddrW = 9;

  logic [NumAlerts-1:0] alert_test, alerts;

  // Registers.
  i3c_reg2hw_t reg2hw;
  i3c_hw2reg_t hw2reg;
  // Memory windows.
  tlul_pkg::tl_h2d_t tl_win_h2d[TL_Count];
  tlul_pkg::tl_d2h_t tl_win_d2h[TL_Count];

  i3c_reg_top #(
    .EnableRacl       (EnableRacl),
    .RaclErrorRsp     (RaclErrorRsp),
    .RaclPolicySelVec (RaclPolicySelVec)
  ) u_reg (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .clk_aon_i        (clk_aon_i),
    .rst_aon_ni       (rst_aon_ni),
    .tl_i             (tl_i),
    .tl_o             (tl_o),

    // Message buffer window.
    .tl_win_o         (tl_win_h2d),
    .tl_win_i         (tl_win_d2h),

    // Registers.
    .reg2hw           (reg2hw),
    .hw2reg           (hw2reg),

    // RACL interface.
    .racl_policies_i  (racl_policies_i),
    .racl_error_o     (racl_error_o),

    // Integrity checking.
    .intg_err_o       (alerts[0])
  );

  // Software access to the Device Address Table.
  logic                    sw_dat_req;
  logic                    sw_dat_gnt;
  logic                    sw_dat_we;
  logic       [DATAddrW:0] sw_dat_addr;
  logic    [DataWidth-1:0] sw_dat_wdata;
  logic                    sw_dat_rvalid;
  logic    [DataWidth-1:0] sw_dat_rdata;

  // Software access to the Device Characteristics Table.
  logic                    sw_dct_req;
  logic                    sw_dct_gnt;
  logic                    sw_dct_we;
  logic     [DCTAddrW+1:0] sw_dct_addr;
  logic    [DataWidth-1:0] sw_dct_wdata;
  logic                    sw_dct_rvalid;
  logic    [DataWidth-1:0] sw_dct_rdata;

  // Direct software interface to the message buffer.
  logic                    sw_buf_req;
  logic                    sw_buf_gnt;
  logic                    sw_buf_we;
  logic   [SWDirAddrW-1:0] sw_buf_addr;
  logic    [DataWidth-1:0] sw_buf_wdata;
  logic                    sw_buf_rvalid;
  logic              [1:0] sw_buf_rerror;
  logic    [DataWidth-1:0] sw_buf_rdata;

  // Word-based windows; each of these must be capable of stalling the TL-UL interface briefly
  // whilst arbitrating for access to the shared message buffer.
  //
  // HCI TL-UL window implements the following:
  // - COMMAND_QUEUE_PORT.
  // - RESPONSE_QUEUE_PORT.
  // - XFER_DATA_PORT access to the message buffer.
  // - IBI_PORT.
  //
  // TTI TL-UL window implements:
  // - RX_DATA_DESC.
  // - RX_DATA_PORT.
  // - IBI_DESC.
  // - IBI_DATA_PORT.
  // - ASYNC_EVENT_QUEUE.
  // - TX[3:0]_DATA_DESC.
  // - TX[3:0]_DATA_PORT.

  logic                   bufq_req[TL_WordCnt];
  logic                   bufq_gnt[TL_WordCnt];
  logic                    bufq_we[TL_WordCnt];
  logic           [3:0]  bufq_addr[TL_WordCnt];
  logic [DataWidth-1:0] bufq_wdata[TL_WordCnt];
  logic [DataWidth-1:0] bufq_rdata[TL_WordCnt];
  logic                bufq_rvalid[TL_WordCnt];

  for (genvar t = 0; t < TL_WordCnt; t++) begin : gen_tlul_win
    tlul_adapter_sram #(
      .SramAw(4),
      .SramDw(DataWidth),
      .Outstanding(2),
      .ByteAccess(0)
    ) u_tlul_win (
      .clk_i,
      .rst_ni,

      .tl_i                       (tl_win_h2d[t]),
      .tl_o                       (tl_win_d2h[t]),
      .en_ifetch_i                (prim_mubi_pkg::MuBi4False),
      .req_o                      (bufq_req[t]),
      .req_type_o                 (),
      .gnt_i                      (bufq_gnt[t]),
      .we_o                       (bufq_we[t]),
      .addr_o                     (bufq_addr[t]),
      .wdata_o                    (bufq_wdata[t]),
      .wmask_o                    (),
      .intg_error_o               (),
      .user_rsvd_o                (),
      .rdata_i                    (bufq_rdata[t]),
      .rvalid_i                   (bufq_rvalid[t]),
      .rerror_i                   ('0),
      .compound_txn_in_progress_o (),
      .readback_en_i              (prim_mubi_pkg::MuBi4False),
      .readback_error_o           (),
      .wr_collision_i             (1'b0),
      .write_pending_i            (1'b0)
    );
  end

  // Device Address Table access.
  tlul_adapter_sram #(
    .SramAw(DATAddrW+1),
    .SramDw(DataWidth),
    .Outstanding(2),
    .ByteAccess(0)
  ) u_tlul2dat (
    .clk_i,
    .rst_ni,

    .tl_i                       (tl_win_h2d[TL_DAT]),
    .tl_o                       (tl_win_d2h[TL_DAT]),
    .en_ifetch_i                (prim_mubi_pkg::MuBi4False),
    .req_o                      (sw_dat_req),
    .req_type_o                 (),
    .gnt_i                      (sw_dat_gnt),
    .we_o                       (sw_dat_we),
    .addr_o                     (sw_dat_addr),
    .wdata_o                    (sw_dat_wdata),
    .wmask_o                    (),
    .intg_error_o               (),
    .user_rsvd_o                (),
    .rdata_i                    (sw_dat_rdata),
    .rvalid_i                   (sw_dat_rvalid),
    .rerror_i                   (2'b00),
    .compound_txn_in_progress_o (),
    .readback_en_i              (prim_mubi_pkg::MuBi4False),
    .readback_error_o           (),
    .wr_collision_i             (1'b0),
    .write_pending_i            (1'b0)
  );

  // Device Characteristics Table access.
  tlul_adapter_sram #(
    .SramAw(DCTAddrW+2),
    .SramDw(DataWidth),
    .Outstanding(2),
    .ByteAccess(0)
  ) u_tlul2dct (
    .clk_i,
    .rst_ni,

    .tl_i                       (tl_win_h2d[TL_DCT]),
    .tl_o                       (tl_win_d2h[TL_DCT]),
    .en_ifetch_i                (prim_mubi_pkg::MuBi4False),
    .req_o                      (sw_dct_req),
    .req_type_o                 (),
    .gnt_i                      (sw_dct_gnt),
    .we_o                       (sw_dct_we),
    .addr_o                     (sw_dct_addr),
    .wdata_o                    (sw_dct_wdata),
    .wmask_o                    (),
    .intg_error_o               (),
    .user_rsvd_o                (),
    .rdata_i                    (sw_dct_rdata),
    .rvalid_i                   (sw_dct_rvalid),
    .rerror_i                   (2'b00),
    .compound_txn_in_progress_o (),
    .readback_en_i              (prim_mubi_pkg::MuBi4False),
    .readback_error_o           (),
    .wr_collision_i             (1'b0),
    .write_pending_i            (1'b0)
  );

  // Direct Software access to the message buffer is optional.
  // - May be useful for lower-level control of I3C traffic.
  // - Diagnostic/debug use.
  if (SWDirectMsgBuf) begin : gen_swdirect
    tlul_adapter_sram #(
      .SramAw(SWDirAddrW),
      .SramDw(DataWidth),
      .Outstanding(2),
      .ByteAccess(0)
    ) u_tlul2sram (
      .clk_i,
      .rst_ni,

      .tl_i                       (tl_win_h2d[TL_SwBuf]),
      .tl_o                       (tl_win_d2h[TL_SwBuf]),
      .en_ifetch_i                (SWDirEnIFetch),
      .req_o                      (sw_buf_req),
      .req_type_o                 (),
      .gnt_i                      (sw_buf_gnt),
      .we_o                       (sw_buf_we),
      .addr_o                     (sw_buf_addr),
      .wdata_o                    (sw_buf_wdata),
      .wmask_o                    (),
      .intg_error_o               (),
      .user_rsvd_o                (),
      .rdata_i                    (sw_buf_rdata),
      .rvalid_i                   (sw_buf_rvalid),
      .rerror_i                   (sw_buf_rerror),
      .compound_txn_in_progress_o (),
      .readback_en_i              (prim_mubi_pkg::MuBi4False),
      .readback_error_o           (),
      .wr_collision_i             (1'b0),
      .write_pending_i            (1'b0)
    );
  end else begin : gen_no_swdirect
    wire swbuf_unused = ^{sw_buf_rdata, sw_buf_rvalid, sw_buf_rerror};
    assign {sw_buf_req, sw_buf_we, sw_buf_addr, sw_buf_wdata} = '0;
    tlul_err_resp u_err_sw_buf(
      .clk_i,
      .rst_ni,
      .tl_h_i (tl_win_h2d[TL_SwBuf]),
      .tl_h_o (tl_win_d2h[TL_SwBuf])
    );
  end

  // The core I3C logic.
  i3c_core #(
    .ClkFreq          (ClkFreq),
    .BufAddrW         (BufAddrW),
    .DataWidth        (DataWidth),
    .NumTargets       (NumTargets),
    .NumSDALanes      (1),
    .NumDATEntries    (NumDATEntries),
    .NumDCTEntries    (NumDCTEntries),
    .SWDirAddrW       (SWDirAddrW),
    .CompManufacturer (CompManufacturer),
    .CompVersion      (CompVersion),
    .CompType         (CompType)
  ) u_core (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),

    // Configuration.
    .reg2hw_i         (reg2hw),
    .hw2reg_o         (hw2reg),

    // HCI Command Queue Port access.
    // HCI Response Queue Port access.
    // HCI XFER_DATA_PORT access.
    // HCI IBI Port access.
    // Target TX_DATA_PORT access.
    // Target RX_DATA_PORT access.
    .bufq_req_i       (bufq_req),
    .bufq_gnt_o       (bufq_gnt),
    .bufq_we_i        (bufq_we),
    .bufq_addr_i      (bufq_addr),
    .bufq_wdata_i     (bufq_wdata),
    .bufq_rvalid_o    (bufq_rvalid),
    .bufq_rdata_o     (bufq_rdata),

    // HCI DAT access from software.
    .sw_dat_req_i     (sw_dat_req),
    .sw_dat_gnt_o     (sw_dat_gnt),
    .sw_dat_we_i      (sw_dat_we),
    .sw_dat_addr_i    (sw_dat_addr),
    .sw_dat_wdata_i   (sw_dat_wdata),
    .sw_dat_rvalid_o  (sw_dat_rvalid),
    .sw_dat_rdata_o   (sw_dat_rdata),

    // HCI DCT access from software.
    .sw_dct_req_i     (sw_dct_req),
    .sw_dct_gnt_o     (sw_dct_gnt),
    .sw_dct_we_i      (sw_dct_we),
    .sw_dct_addr_i    (sw_dct_addr),
    .sw_dct_wdata_i   (sw_dct_wdata),
    .sw_dct_rvalid_o  (sw_dct_rvalid),
    .sw_dct_rdata_o   (sw_dct_rdata),

    // Direct software interface to message buffer.
    .sw_buf_req_i     (sw_buf_req),
    .sw_buf_gnt_o     (sw_buf_gnt),
    .sw_buf_we_i      (sw_buf_we),
    .sw_buf_addr_i    (sw_buf_addr),
    .sw_buf_wdata_i   (sw_buf_wdata),
    .sw_buf_rvalid_o  (sw_buf_rvalid),
    .sw_buf_rerror_o  (sw_buf_rerror),
    .sw_buf_rdata_o   (sw_buf_rdata),

    // I3C Controller I/O signaling.
    .ctrl_bus_drv_o   (cio_ctrl_bus_drv_o),
    .ctrl_bus_obv_i   (cio_ctrl_bus_obv_i),

    // Pull-up enables for open drain intervals.
    .ctrl_scl_pu_en_o (cio_ctrl_scl_pu_en_o),
    .ctrl_sda_pu_en_o (cio_ctrl_sda_pu_en_o),

    // High-keeper enables.
    .scl_hk_en_o      (cio_scl_hk_en_o),
    .sda_hk_en_o      (cio_sda_hk_en_o),

    // I3C Target I/O signaling.
    .targ_bus_drv_o   (cio_targ_bus_drv_o),
    .targ_bus_obv_i   (cio_targ_bus_obv_i),

    // Target Reset Detector request/response.
    .rstdet_enable_o  (rstdet_enable_o),
    .rstdet_req_o     (rstdet_req_o),
    .rstdet_rsp_i     (rstdet_rsp_i),

    // Interrupts.
    .intr_hci_o       (intr_hci_o),
    .intr_targ_o      (intr_targ_o),

    // DFT-related controls.
    .ram_cfg_i        (ram_cfg_i),
    .ram_cfg_rsp_o    (ram_cfg_rsp_o),
    .dat_cfg_i        (dat_cfg_i),
    .dat_cfg_rsp_o    (dat_cfg_rsp_o),
    .dct_cfg_i        (dct_cfg_i),
    .dct_cfg_rsp_o    (dct_cfg_rsp_o),
    .mbist_en_i       (mbist_en_i),
    .scan_clk_i       (scan_clk_i),
    .scan_rst_ni      (scan_rst_ni),
    .scanmode_i       (scanmode_i)
  );

  // Alerts
  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .SkewCycles(AlertSkewCycles),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // Assert Known for I3C Controller outputs
  `ASSERT_KNOWN(CtrlSCLEnKnown_A, cio_ctrl_bus_drv_o.scl_en, clk_i, !rst_ni)
  `ASSERT_KNOWN(CtrlSCLKnown_A, cio_ctrl_bus_drv_o.scl, clk_i, !rst_ni ||
                !cio_ctrl_bus_drv_o.scl_en)

  `ASSERT_KNOWN(CtrlSDAPPEnKnown_A, cio_ctrl_bus_drv_o.sda_pp_en, clk_i, !rst_ni)
  `ASSERT_KNOWN(CtrlSDAODEnKnown_A, cio_ctrl_bus_drv_o.sda_od_en, clk_i, !rst_ni)
  `ASSERT_KNOWN(CtrlSDAKnown_A, cio_ctrl_bus_drv_o.sda, clk_i, !rst_ni ||
                (!cio_ctrl_bus_drv_o.sda_pp_en & !cio_ctrl_bus_drv_o.sda_od_en))

  // Assert Known for I3C Target outputs
  `ASSERT_KNOWN(TargSDAPPEnKnown_A, cio_targ_bus_drv_o.sda_pp_en, clk_i, !rst_ni)
  `ASSERT_KNOWN(TargSDAODEnKnown_A, cio_targ_bus_drv_o.sda_od_en, clk_i, !rst_ni)
  `ASSERT_KNOWN(TargSDAKnown_A, cio_targ_bus_drv_o.sda, clk_i, !rst_ni ||
                (!cio_targ_bus_drv_o.sda_pp_en & !cio_targ_bus_drv_o.sda_od_en))

  // Assert Known for alerts
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])

  // Assert Known for interrupts
  `ASSERT_KNOWN(DoneKnown_A, intr_hci_o)

  // Check that the bus width meets the requirements of the message buffer, DAT and DCT tables.
  if (DataWidth != 32) $fatal(1, "This design presently supports only 32-bit system buses.");

endmodule
