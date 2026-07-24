// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I3C Controller and Target.
//
// This IP block has been designed and built for compliance with the following specifications:
//
// - MIPI Alliance Specification for I3C Basic, Version 1.2 Public Release Edition.
// - MIPI Alliance Specification for I3C TCRI, Version 1.0 (Public Release Edition).
// - MIPI Alliance Specification for I3C HCI, Version 1.2 (Public Release Edition).

module i3c_core
  import i3c_io_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
  import prim_mubi_pkg::*;
  import prim_ram_1p_pkg::*;
#(
  parameter int unsigned ClkFreq          = 50_000_000,  // IP clock frequency, Hz.
  parameter int unsigned BufAddrW         = i3c_pkg::BufAddrW,
  parameter int unsigned DataWidth        = 32,
  parameter int unsigned NumSDALanes      = 1,
  parameter int unsigned NumTargets       = i3c_pkg::NumTargets,
  parameter int unsigned NumDATEntries    = i3c_pkg::NumDATEntries,
  parameter int unsigned NumDCTEntries    = i3c_pkg::NumDCTEntries,
  parameter int unsigned SWDirAddrW       = 9,
  parameter int unsigned CompManufacturer = '0,  // MIPI Manufacturer ID.
  parameter int unsigned CompVersion      = '0,  // Component Version.
  parameter int unsigned CompType         = '0,  // Product ID or Type.

  // Derived parameters.
  localparam int unsigned DATAddrW = $clog2(NumDATEntries),
  localparam int unsigned DCTAddrW = $clog2(NumDCTEntries)
) (
  // Clock and reset for system interface.
  input                     clk_i,
  input                     rst_ni,

  // Configuration.
  input  i3c_reg2hw_t       reg2hw_i,
  output i3c_hw2reg_t       hw2reg_o,

  // HCI Command Queue Port access.
  // HCI Response Queue Port access.
  // HCI XFER_DATA_PORT access.
  // HCI IBI Port access.
  // Target TX_DATA_PORT access.
  // Target RX_DATA_PORT access.
  input                     bufq_req_i[TL_WordCnt],
  output                    bufq_gnt_o[TL_WordCnt],
  input                     bufq_we_i[TL_WordCnt],
  input               [3:0] bufq_addr_i[TL_WordCnt],
  input     [DataWidth-1:0] bufq_wdata_i[TL_WordCnt],
  output                    bufq_rvalid_o[TL_WordCnt],
  output    [DataWidth-1:0] bufq_rdata_o[TL_WordCnt],

  // HCI Device Address Table interface.
  input                     sw_dat_req_i,
  output                    sw_dat_gnt_o,
  input                     sw_dat_we_i,
  input        [DATAddrW:0] sw_dat_addr_i,
  input     [DataWidth-1:0] sw_dat_wdata_i,
  output                    sw_dat_rvalid_o,
  output    [DataWidth-1:0] sw_dat_rdata_o,

  // HCI Device Characteristics Table interface
  input                     sw_dct_req_i,
  output                    sw_dct_gnt_o,
  input                     sw_dct_we_i,
  input      [DCTAddrW+1:0] sw_dct_addr_i,
  input     [DataWidth-1:0] sw_dct_wdata_i,
  output                    sw_dct_rvalid_o,
  output    [DataWidth-1:0] sw_dct_rdata_o,

  // Direct software interface to buffer.
  input                     sw_buf_req_i,
  output                    sw_buf_gnt_o,
  input                     sw_buf_we_i,
  input    [SWDirAddrW-1:0] sw_buf_addr_i,
  input     [DataWidth-1:0] sw_buf_wdata_i,
  output                    sw_buf_rvalid_o,
  output              [1:0] sw_buf_rerror_o,
  output    [DataWidth-1:0] sw_buf_rdata_o,

  // I3C Controller I/O signaling.
  output i3c_ctrl_bus_drv_t ctrl_bus_drv_o,
  input  i3c_ctrl_bus_obv_t ctrl_bus_obv_i,

  // Pull-up enables.
  output                    ctrl_scl_pu_en_o,
  output                    ctrl_sda_pu_en_o,

  // High-keeper enables.
  output                    scl_hk_en_o,
  output                    sda_hk_en_o,

  // I3C Target I/O signaling.
  output i3c_targ_bus_drv_t targ_bus_drv_o,
  input  i3c_targ_bus_obv_t targ_bus_obv_i,

  // Target Reset Detector request/response.
  output                    rstdet_enable_o,
  output i3c_rstdet_req_t   rstdet_req_o,
  input  i3c_rstdet_rsp_t   rstdet_rsp_i,

  // Interrupts.
  output                    intr_hci_o,
  output                    intr_targ_o,

  // DFT-related controls.
  input  ram_1p_cfg_t       ram_cfg_i,
  output ram_1p_cfg_rsp_t   ram_cfg_rsp_o,
  input  ram_1p_cfg_t       dat_cfg_i,
  output ram_1p_cfg_rsp_t   dat_cfg_rsp_o,
  input  ram_1p_cfg_t       dct_cfg_i,
  output ram_1p_cfg_rsp_t   dct_cfg_rsp_o,
  input                     mbist_en_i,
  input                     scan_clk_i,
  input                     scan_rst_ni,
  input mubi4_t             scanmode_i
);

  import i3c_consts_pkg::*;
  import i3c_controller_pkg::*;
  import i3c_fifo_pkg::*;
  import i3c_target_pkg::*;

  localparam int unsigned FIFODepthW = i3c_fifo_pkg::DepthW;

  // DFT-related signals.
  // TODO: sync?
  wire scanmode = prim_mubi_pkg::mubi4_test_true_strict(scanmode_i);

  // Software resets for Controller and Target logic.
  wire ctrl_sw_reset = reg2hw_i.reset_control.soft_rst.qe & reg2hw_i.reset_control.soft_rst.q;
  wire targ_sw_reset = reg2hw_i.reset_control.soft_rst.qe & reg2hw_i.reset_control.soft_rst.q;

  // High-level enable signals.
  logic enabling, ctrl_enabled, stby_cr_enabled, targ_enabled, buf_enabled, inbuf_enable;
  assign targ_enabled = reg2hw_i.targ_control.en.q | stby_cr_enabled;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) buf_enabled <= 1'b0;
    else buf_enabled <= ctrl_enabled | targ_enabled;
  end
  assign enabling = (ctrl_enabled | targ_enabled) & !buf_enabled;

  // Is the final Target operating as a Standby Controller?
  i3c_stby_cr_en_init_e stby_cr_en_init;
  assign stby_cr_en_init = i3c_stby_cr_en_init_e'(hw2reg_o.stby_cr_control.stby_cr_enable_init.d);
  assign stby_cr_enabled = (stby_cr_en_init inside {StbyCrEn_SCMRunning, StbyCrEn_SCMHotJoin});

  // Synchronize the SCL and SDA signals to the IP block, for monitoring of bus available/idle
  // condition, detection of Start Requests, and to present them in the debug state.
  //
  // Note: we _could_ introduce some filtering on this signal path, since we have up to 1us to
  // drive the clock signal in response to SDA falling.
  logic ctrl_sda_sync, ctrl_scl_sync;
  prim_flop_2sync #(.Width(2)) u_sync_ctrl(
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    ({ctrl_bus_obv_i.sda[0], ctrl_bus_obv_i.scl}),
    .q_o    ({ctrl_sda_sync,         ctrl_scl_sync})
  );
  assign hw2reg_o.present_state_debug.sda_line_signal_level.d = ctrl_sda_sync;
  assign hw2reg_o.present_state_debug.scl_line_signal_level.d = ctrl_scl_sync;

  logic targ_sda_sync, targ_scl_sync;
  prim_flop_2sync #(.Width(2)) u_sync_targ(
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    ({targ_bus_obv_i.sda[0], targ_bus_obv_i.scl}),
    .q_o    ({targ_sda_sync, targ_scl_sync})
  );
  assign hw2reg_o.targ_state_debug.sda_line_signal_level.d = targ_sda_sync;
  assign hw2reg_o.targ_state_debug.scl_line_signal_level.d = targ_scl_sync;

  // Bus timing; any deviation from both signals being high (inactive) resets the timers for
  // the following conditions:
  // - Bus Available (after 1us of inactivity).
  // - Bus Idle (after 200us of inactivity).
  // - TE0 Recovery (after 60us of inactivity).
  //
  // Note: when the logic attached to a bus is disabled, the bus is considered to be `active`
  //       because we are timing a period of inactivity from the point of becoming enabled.
  logic ctrl_bus_active;
  logic ctrl_bus_avail;
  assign ctrl_bus_active = ~(ctrl_enabled & ctrl_sda_sync & ctrl_scl_sync);

  logic targ_bus_active;
  logic targ_bus_avail, targ_bus_idle;
  logic targ_rst_bus_avail;
  assign targ_bus_active = ~(targ_enabled & targ_sda_sync & targ_scl_sync);

  logic targ_scl_buf, targ_scl_buf_n;    // Posedge and negedge SCL clock signals.
  logic targ_sda0_clk, targ_sda0_clk_n;  // Posedge and negedge SDA signals, suitable for clocking.
  logic [NumSDALanes-1:0] targ_sda_buf;  // Buffered SDA lanes, to avoid SCL-relative skew.
  logic targ_reset_trx;                  // Initiate reset of Target-side transceiver logic.
  logic targ_trx_rst_n;                  // Asynchronous reset into Target-side transceiver.

  // We measure tAVAL from the most recently bus active _and_ the most recent transceiver reset.
  assign targ_rst_bus_avail = targ_bus_active | !targ_trx_rst_n;

  // Report measured duration of bus inactivity, for diagnostic use.
  assign hw2reg_o.targ_state_debug.bus_idle.d  = targ_bus_idle;
  assign hw2reg_o.targ_state_debug.bus_avail.d = targ_bus_avail;

  // Diagnostic visibility into the Target state.
  logic [7:0] targ_trx_state;
  logic [3:0] targ_bus_mode;
  prim_flop_2sync #(.Width(12)) u_reg_sync (  // TODO: Narrow the state variable?
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    ({targ_trx_state, targ_bus_mode}),
    .q_o    ({hw2reg_o.targ_state_debug.trx_state.d,
              hw2reg_o.targ_state_debug.bus_mode.d})
  );

  // Reset generation for SCL-driven logic
  // - since SCL is supplied by whichever Controller is actively driving the bus, it is asynchronous
  //   with respect to any asynchronous reset, sw-initiated reset or recovery mechanism that is
  //   required, so we re-enable the buffers only when we the bus has been idle for tAVAL (4.3.3.2).
  i3c_target_rst u_targ_rst(
    // Main IP clock and reset.
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    // Control.
    .enable_i     (targ_enabled),
    .sw_reset_i   (targ_sw_reset),
    // TODO: Error conditions requiring a reset shall be received and handled here.

    // Bus monitoring.
    .bus_avail_i  (targ_bus_avail),

    // Initiate asynchronous reset of Target-side transceiver logic.
    .reset_trx_o  (targ_reset_trx),

    // Buffer enable for SCL and SDA into the SCL-driven target transceiver logic.
    .inbuf_en_o   (inbuf_enable)
  );

  // Controller-side I3C input buffering.
  logic [NumSDALanes-1:0] ctrl_sda_buf;
  buf_en #(.Width(NumSDALanes)) u_ctrl_inbufs (
    // Enable input propagation.
    // TODO: Probably want to gate off the SDA lane when the bus is available and the Controller
    //       does not need to drive it. We need a transceiver output to achieve this.
    .en_i   (ctrl_enabled),
    .in_i   (ctrl_bus_obv_i.sda),
    .out_o  (ctrl_sda_buf)
  );

  // Target-side I3C input buffering.
  i3c_input_buffers #(.NumSDALanes(NumSDALanes)) u_targ_inbufs (
    // Enable input propagation.
    .enable_i     (inbuf_enable),

    // I3C target inputs.
    .scl_i        (targ_bus_obv_i.scl),
    .sda_i        (targ_bus_obv_i.sda),

    // Clock signals.
    .scl_buf_o    (targ_scl_buf),
    .scl_buf_no   (targ_scl_buf_n),
    .sda0_clk_o   (targ_sda0_clk),
    .sda0_clk_no  (targ_sda0_clk_n),
    // Buffered input data (SDA), to avoid SCL-relative skew.
    .sda_buf_o    (targ_sda_buf),

    // DFT-related signals.
    .scan_clk_i   (scan_clk_i),
    .scanmode_i   (scanmode)
  );

  // Enable for the Target Reset Detector.
  // TODO: When the IP block is in a sleep state, the `enable` assertion will need to be maintained.
  assign rstdet_enable_o = inbuf_enable;

  // TTI interrupt signal.
  i3c_targ_intr_t targ_interrupts;
  // HCI Interrupt signals.
  i3c_stby_cr_intr_t stby_cr_interrupts;
  i3c_pio_intr_t pio_interrupts;
  i3c_hc_intr_t hc_interrupts;

  // `SDA Read Detector` (4.3.2.3) indicates whether a Private Read operation in SDR mode has
  // stalled, i.e. no SCL activity observed for at least 100us.
  logic rst_read_stalled;
  logic read_stalled;
  assign rst_read_stalled = 1'b0;

  // `Dead Bus Recovery` (4.3.8.1.8)
  // - after 50ms with SDA continuously low and SCL continuously high, implying the failure of the
  //   Active Controller to respond to a Start request, a Standby Controller can attempt to
  //   transition to the role of Active Controller.
  logic rst_dead_bus;
  logic dead_bus;
  assign rst_dead_bus = targ_sda_sync | !targ_scl_sync;

  // Controller, Target and software access to FIFOs.
  fifo_state_t  fifo_state[FIFO_Count];
  fifo_out_t    fifo_out[FIFO_Count];
  fifo_in_t     fifo_in[FIFO_Count];
  fifo_config_t fifo_cfg[FIFO_Count];
  logic         fifo_rst[FIFO_Count];

  // Signals from pattern detector, synchronized to main clock.
  logic hdr_restart_det;
  logic hdr_exit_det;

  // High-keeper enables; see section 4.3.3.1.
  assign scl_hk_en_o = reg2hw_i.phy_config.scl_hk_en.q;
  assign sda_hk_en_o = reg2hw_i.phy_config.sda_hk_en.q;

  // List of blocked addresses with which neither the Controller nor the Target shall communicate;
  // this is a safeguard against I2C devices that may use clock-stretching, but may also be of use
  // diagnostically.
  logic [6:0] addr_blocked[NumBlocked];
  logic [6:0] mask_blocked[NumBlocked];  // Masks determine which address bits are tested.
  assign addr_blocked[1] = reg2hw_i.blocked_addr.addr1;
  assign addr_blocked[0] = reg2hw_i.blocked_addr.addr0;
  assign mask_blocked[1] = reg2hw_i.blocked_addr.mask1;
  assign mask_blocked[0] = reg2hw_i.blocked_addr.mask0;

  // Controller state signals.
  logic ac_current_own;
  // Next entry within DCT to be completed during Dynamic Address Assignment.
  logic [4:0] dct_idx;

  // Broadcast CCCs received in Standby Controller mode.
  // - these are passed from the Target-side logic to the HCI IBI Queue.
  logic                 stby_bcst_wvalid;
  logic [DataWidth-1:0] stby_bcst_wdata;
  logic                 stby_bcst_wready;

  // Interface between controller logic and transceiver.
  logic                ctrl_trx_sreq;   // Start request from Target, via transceiver.
  i3c_ctrl_trx_req_t   ctrl_trx_dreq;   // Request to the transceiver.
  i3c_ctrl_trx_arb_t   ctrl_trx_arb;    // Arbitration request to the core.
  i3c_ctrl_trx_rdata_t ctrl_trx_rdata;  // Read data from the transceiver.
  i3c_ctrl_trx_rsp_t   ctrl_trx_rsp;    // Response to the core.

  logic ctrl_trx_dvalid, ctrl_trx_dready;
  logic ctrl_trx_avalid, ctrl_trx_aready;
  logic ctrl_trx_rdvalid;
  logic ctrl_trx_rvalid, ctrl_trx_rready;

  logic ctrl_trx_arb_nack;  // TODO: Temporary.

  // Controller Error counting (CE[3:0], Table 44).
  logic [3:0] ctrl_error;

  // Controller core.
  i3c_controller #(
    .DataWidth          (DataWidth),
    .FIFODepthW         (FIFODepthW),
    .NumDATEntries      (NumDATEntries),
    .NumDCTEntries      (NumDCTEntries)
  ) u_controller (
    // Clock and reset for system interface.
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),

    // Control inputs.
    .sw_reset_i         (ctrl_sw_reset),
    .fifo_rst_i         (fifo_rst),

    // Configuration settings.
    .reg2hw_i           (reg2hw_i),
    .dct_idx_qe_i       (reg2hw_i.dct_section_offset.table_index.qe),
    .dct_idx_q_i        (reg2hw_i.dct_section_offset.table_index.q),

    // Blocked addresses.
    .addr_blocked_i     (addr_blocked),
    .mask_blocked_i     (mask_blocked),

    // State information, presented via HCI.
    .enabled_o          (ctrl_enabled),
    .ac_current_own_o   (ac_current_own),
    .dct_idx_o          (dct_idx),
    .hc_control_o       (hw2reg_o.hc_control),

    // Command Queue access.
    .cmd_desc_rready_o  (fifo_in[FIFO_CmdQ].rready),
    .cmd_desc_rvalid_i  (fifo_out[FIFO_CmdQ].rvalid),
    .cmd_desc_rdata_i   (fifo_out[FIFO_CmdQ].rdata),
    .cmd_desc_ravail_i  (fifo_state[FIFO_CmdQ].avail),

    // Response Queue access.
    .rsp_desc_wvalid_o  (fifo_in[FIFO_RspQ].wvalid),
    .rsp_desc_wdata_o   (fifo_in[FIFO_RspQ].wdata),
    .rsp_desc_wready_i  (fifo_out[FIFO_RspQ].wready),
    .rsp_desc_wused_i   (fifo_state[FIFO_RspQ].used),
    .rsp_desc_wfull_i   (fifo_state[FIFO_RspQ].full),

    // IBI Queue access.
    .ibi_data_wvalid_o  (fifo_in[FIFO_IBIQ].wvalid),
    .ibi_data_wdata_o   (fifo_in[FIFO_IBIQ].wdata),
    .ibi_data_wready_i  (fifo_out[FIFO_IBIQ].wready),
    .ibi_data_wfull_i   (fifo_state[FIFO_IBIQ].full),

    // IBI Status Descriptor FIFO access.
    .ibi_stat_wvalid_o  (fifo_in[FIFO_IBIStD].wvalid),
    .ibi_stat_wdata_o   (fifo_in[FIFO_IBIStD].wdata),
    .ibi_stat_wready_i  (fifo_out[FIFO_IBIStD].wready),
    .ibi_stat_wused_i   (fifo_state[FIFO_IBIStD].used),
    .ibi_stat_wfull_i   (fifo_state[FIFO_IBIStD].full),

    // HCI Device Address Table interface.
    .sw_dat_req_i       (sw_dat_req_i),
    .sw_dat_gnt_o       (sw_dat_gnt_o),
    .sw_dat_we_i        (sw_dat_we_i),
    .sw_dat_addr_i      (sw_dat_addr_i),
    .sw_dat_wdata_i     (sw_dat_wdata_i),
    .sw_dat_rvalid_o    (sw_dat_rvalid_o),
    .sw_dat_rdata_o     (sw_dat_rdata_o),

    // HCI Device Characteristics Table interface.
    .sw_dct_req_i       (sw_dct_req_i),
    .sw_dct_gnt_o       (sw_dct_gnt_o),
    .sw_dct_we_i        (sw_dct_we_i),
    .sw_dct_addr_i      (sw_dct_addr_i),
    .sw_dct_wdata_i     (sw_dct_wdata_i),
    .sw_dct_rvalid_o    (sw_dct_rvalid_o),
    .sw_dct_rdata_o     (sw_dct_rdata_o),

    // Interrupt signals.
    .intr_hc_o          (hc_interrupts),
    .intr_pio_o         (pio_interrupts),
    .intr_stby_cr_o     (stby_cr_interrupts),

    // Reading from Tx Buffer.
    .txbuf_rready_o     (fifo_in[FIFO_TxBuf].rready),
    .txbuf_rvalid_i     (fifo_out[FIFO_TxBuf].rvalid),
    .txbuf_rdata_i      (fifo_out[FIFO_TxBuf].rdata),
    .txbuf_rempty_i     (fifo_state[FIFO_TxBuf].empty),
    .txbuf_rused_i      (fifo_state[FIFO_TxBuf].used),
    .txbuf_ravail_i     (fifo_state[FIFO_TxBuf].avail),

    // Writing to Rx Buffer.
    .rxbuf_wvalid_o     (fifo_in[FIFO_RxBuf].wvalid),
    .rxbuf_wdata_o      (fifo_in[FIFO_RxBuf].wdata),
    .rxbuf_wready_i     (fifo_out[FIFO_RxBuf].wready),
    .rxbuf_wused_i      (fifo_state[FIFO_RxBuf].used),
    .rxbuf_wfull_i      (fifo_state[FIFO_RxBuf].full),
    .rxbuf_wavail_i     (fifo_state[FIFO_RxBuf].avail),

    // Broadcast CCCs received in Standby Controller mode.
    .stby_bcst_wvalid_i (stby_bcst_wvalid),
    .stby_bcst_wdata_i  (stby_bcst_wdata),
    .stby_bcst_wready_o (stby_bcst_wready),

    // Start request signaling from target.
    .trx_sreq_i         (ctrl_trx_sreq),

    // Request to the transceiver logic.
    .trx_dvalid_o       (ctrl_trx_dvalid),
    .trx_dready_i       (ctrl_trx_dready),
    .trx_dreq_o         (ctrl_trx_dreq),

    // Arbitration requests from the transceiver logic.
    .trx_avalid_i       (ctrl_trx_avalid),
    .trx_arb_i          (ctrl_trx_arb),
    .trx_aready_o       (ctrl_trx_aready),
    .trx_arb_nack_o     (ctrl_trx_arb_nack),

    // Read data from the transceiver logic.
    .trx_rdvalid_i      (ctrl_trx_rdvalid),
    .trx_rdata_i        (ctrl_trx_rdata),

    // Response from the transceiver logic.
    .trx_rvalid_i       (ctrl_trx_rvalid),
    .trx_rready_o       (ctrl_trx_rready),
    .trx_rsp_i          (ctrl_trx_rsp),

    // Debug status information.
    .cmd_tid_o          ({hw2reg_o.present_state_debug.cmd_tid.d}),
    .bcl_tfr_ststat_o   ({hw2reg_o.present_state_debug.bcl_tfr_st_status.d}),
    .ce2_error_cnt_o    ({hw2reg_o.mx_error_counters.d}),
    .ctrl_error_o       (ctrl_error),

    // DFT-related signals.
    .dat_cfg_i          (dat_cfg_i),
    .dat_cfg_rsp_o      (dat_cfg_rsp_o),
    .dct_cfg_i          (dct_cfg_i),
    .dct_cfg_rsp_o      (dct_cfg_rsp_o)
  );

  // To maintain consistent IBI state, the logic must be reset if either of the constituent FIFOs
  // is reset.
  wire ibi_sw_reset = |{ctrl_sw_reset, fifo_rst[FIFO_IBIQ], fifo_rst[FIFO_IBIStD]};

  // HCI-side handling of In-Band Interrupts.
  // - this manages the interleaved reading from the two physical FIFOs (IBIQ and IBIStD).
  logic [DataWidth-1:0] ibi_rdata;
  logic ibi_status_desc;  // Is the next read word an IBI Status Descriptor?
  logic ibi_read;
  i3c_hci_ibi u_hci_ibi (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    .enable_i     (ctrl_enabled),

    .sw_reset_i   (ibi_sw_reset),

    // Indication of whether the next word is a status descriptor.
    .status_o     (ibi_status_desc),

    // Reading from IBI Status Descriptor FIFO and IBI Queue.
    .read_i       (ibi_read),
    .rdata_i      (ibi_rdata)
  );

  // Status outputs from Target logic.
  logic hdr_exit_det_en;  // Enable HDR Exit Pattern detector.

  // Target device descriptions.
  i3c_targ_dev_t      targ_dev[NumTargets];
  // Group address descriptions.
  i3c_grp_addr_t      grp_addr[NumGroups];

  // Interface between Target logic and transceiver.
  logic               targ_trx_dvalid[NumTargets];
  logic               targ_trx_dready[NumTargets];
  i3c_targ_trx_txd_t  targ_trx_dreq[NumTargets];

  // Direct Read CCC data for all Targets is carried as a single unit.
  logic               targ_trx_ctvalid;
  logic               targ_trx_ctready;
  i3c_targ_trx_txc_t  targ_trx_ctreq;

  // Arbitration requests to the transceiver.
  logic               targ_trx_avalid;
  logic               targ_trx_aready;
  i3c_targ_trx_arb_t  targ_trx_areq;

  // Received data from Target transceiver.
  logic               targ_trx_rtoggle;
  i3c_targ_trx_rxd_t  targ_trx_rxd;

  // Start request to the Target transceiver.
  logic               targ_sreq_sda_od_en;
  logic               targ_sreq_sda;
  // Repeated Start (Sr) detection from the Target transceiver.
  logic               targ_rep_start_det;
  // Stop (P) detection from the Target transceiver.
  logic               targ_stop_det;
  // HDR-DDR mode indication from the Target transceiver.
  logic               targ_ddr_mode;

  // Setting the Standby Controller Dynamic Address.
  logic               stby_cr_dynaddr_de;
  logic         [7:0] stby_cr_dynaddr_d;

  // Interrupts from the target core.
  logic               targ_intr_ibi;
  logic               targ_intr_rx[NumTargets];
  logic               targ_intr_tx[NumTargets];

  // Indicate whether Tx data/descriptors are available for each virtual target.
  logic                 targ_tx_desc_rready[NumTargets];
  logic                 targ_buf_rready[NumTargets];

  logic                 targ_tx_desc_rvalid[NumTargets];
  logic [DataWidth-1:0] targ_tx_desc_rdata[NumTargets];
  logic [FIFODepthW:0]  targ_tx_desc_rused[NumTargets];
  logic [FIFODepthW:0]  targ_tx_desc_ravail[NumTargets];

  logic                 targ_buf_rvalid[NumTargets];
  logic [DataWidth-1:0] targ_buf_rdata[NumTargets];
  logic [FIFODepthW:0]  targ_buf_rused[NumTargets];
  logic [FIFODepthW:0]  targ_buf_ravail[NumTargets];

  always_comb begin
    for (int unsigned t = 0; t < NumTargets; t++) begin
      fifo_in[FIFO_TxDTarg0 + t].rready = targ_tx_desc_rready[t];
      fifo_in[FIFO_TxTarg0  + t].rready = targ_buf_rready[t];

      targ_tx_desc_rvalid[t] = fifo_out[FIFO_TxDTarg0 + t].rvalid;
      targ_tx_desc_rdata[t]  = fifo_out[FIFO_TxDTarg0 + t].rdata;
      targ_tx_desc_rused[t]  = fifo_state[FIFO_TxDTarg0 + t].used;
      targ_tx_desc_ravail[t] = fifo_state[FIFO_TxDTarg0 + t].avail;

      targ_buf_rvalid[t] = fifo_out[FIFO_TxTarg0 + t].rvalid;
      targ_buf_rdata[t]  = fifo_out[FIFO_TxTarg0 + t].rdata;
      targ_buf_rused[t]  = fifo_state[FIFO_TxTarg0 + t].used;
      targ_buf_ravail[t] = fifo_state[FIFO_TxTarg0 + t].avail;
    end
  end

  // Suspend transmission from Virtual Targets.
  logic [NumTargets-1:0] targ_suspend_tx;
  assign hw2reg_o.targ_pio_control.suspended.de = |targ_suspend_tx;
  assign hw2reg_o.targ_pio_control.suspended.d  = reg2hw_i.targ_pio_control.suspended.q
                                                | targ_suspend_tx;
  // Suspend IBI Transmission from target.
  assign hw2reg_o.targ_pio_control.ibi_suspended.d = 1'b1;
  // Abort clearing.
  logic [NumTargets-1:0] targ_abort_clr;
  assign hw2reg_o.targ_pio_control.abort.de = |targ_abort_clr;
  assign hw2reg_o.targ_pio_control.abort.d  = reg2hw_i.targ_pio_control.abort.q & ~targ_abort_clr;
  assign hw2reg_o.targ_pio_control.ibi_abort.d = 1'b0;

  // Shared configuration/status for all Virtual Targets.
  logic [NumTargets-1:0] targ_mwl_de;
  logic [NumTargets-1:0] targ_mrl_de;
  logic [NumTargets-1:0] targ_ibi_de;
  logic           [15:0] targ_mwl_d;
  logic           [15:0] targ_mrl_d;
  logic            [7:0] targ_ibi_d;
  // Group Addressing.
  logic                  targ_grp_addr_de[NumGroups];
  logic                  targ_grp_targ_de[NumGroups];
  logic            [6:0] targ_grp_addr_d[NumGroups];
  logic [NumTargets-1:0] targ_grp_targ_d[NumGroups];

  // Enable/disable Events for a set of Virtual Targets.
  i3c_endis_event_t targ_endis_evt;
  always_comb begin
    for (int unsigned t = 0; t < MaxTargets; t++) begin
      if (t < NumTargets) begin
        hw2reg_o.targ_event_enable[t].enint.de = targ_endis_evt.enint[t] | targ_endis_evt.disint[t];
        hw2reg_o.targ_event_enable[t].enint.d  = targ_endis_evt.enint[t];
        hw2reg_o.targ_event_enable[t].encr.de  = targ_endis_evt.encr[t] | targ_endis_evt.discr[t];
        hw2reg_o.targ_event_enable[t].encr.d   = targ_endis_evt.encr[t];
        hw2reg_o.targ_event_enable[t].enhj.de  = targ_endis_evt.enhj[t] | targ_endis_evt.dishj[t];
        hw2reg_o.targ_event_enable[t].enhj.d   = targ_endis_evt.enhj[t];
      end else hw2reg_o.targ_event_enable[t] = '0;  // Virtual Target not present.
    end
  end

  // Updating of Target dynamic addresses.
  logic [NumTargets-1:0] targ_dynaddr_de;
  logic                  targ_dynaddr_valid_d;
  logic            [6:0] targ_dynaddr_d[NumTargets];
  always_comb begin
    for (int unsigned t = 0; t < MaxTargets; t++) begin
      if (t < NumTargets) begin
        // We may be setting, invalidating or modifying the assigned dynamic address.
        hw2reg_o.targ_addr[t].dynamic_addr.de       = targ_dynaddr_de[t];
        hw2reg_o.targ_addr[t].dynamic_addr.d        = targ_dynaddr_d[t];
        hw2reg_o.targ_addr[t].dynamic_addr_valid.de = targ_dynaddr_de[t];
        hw2reg_o.targ_addr[t].dynamic_addr_valid.d  = targ_dynaddr_valid_d;
      end else hw2reg_o.targ_addr[t] = '0;  // Virtual Target not present.
    end
  end

  // Updating of Target Activity State (ENTASn) and ENDXFER configuration.
  logic [NumTargets-1:0] targ_act_state_de;
  logic            [1:0] targ_act_state_d;
  logic [NumTargets-1:0] targ_endxfer_cand_de;
  logic            [2:0] targ_endxfer_cand_d;
  logic [NumTargets-1:0] targ_endxfer_de;
  logic            [2:0] targ_endxfer_d[NumTargets];
  always_comb begin
    for (int unsigned t = 0; t < MaxTargets; t++) begin
      if (t < NumTargets) begin
        hw2reg_o.targ_info[t].endxfer_cand_crc_early.de = targ_endxfer_cand_de[t];
        hw2reg_o.targ_info[t].endxfer_cand_crc_early.d  = targ_endxfer_cand_d[2];
        hw2reg_o.targ_info[t].endxfer_cand_wr_early_term.de = targ_endxfer_cand_de[t];
        hw2reg_o.targ_info[t].endxfer_cand_wr_early_term.d  = targ_endxfer_cand_d[1];
        hw2reg_o.targ_info[t].endxfer_cand_wr_nack.de = targ_endxfer_cand_de[t];
        hw2reg_o.targ_info[t].endxfer_cand_wr_nack.d  = targ_endxfer_cand_d[0];
        hw2reg_o.targ_info[t].endxfer_crc_early.de = targ_endxfer_de[t];
        hw2reg_o.targ_info[t].endxfer_crc_early.d  = targ_endxfer_d[t][2];
        hw2reg_o.targ_info[t].endxfer_wr_early_term.de = targ_endxfer_de[t];
        hw2reg_o.targ_info[t].endxfer_wr_early_term.d  = targ_endxfer_d[t][1];
        hw2reg_o.targ_info[t].endxfer_wr_nack.de = targ_endxfer_de[t];
        hw2reg_o.targ_info[t].endxfer_wr_nack.d  = targ_endxfer_d[t][0];
        hw2reg_o.targ_info[t].as.de = targ_act_state_de[t];
        hw2reg_o.targ_info[t].as.d  = targ_act_state_d[t];
      end else hw2reg_o.targ_info[t] = '0;  // Virtual Target not present.
    end
  end

  // Update RSTACT in response to CCC handling; this is presented in the Standby Cr regs too.
  logic        targ_rstact_de;
  i3c_rstact_e targ_rstact_d;
  assign hw2reg_o.targ_status.rstact.d =
    i3c_rstact_e'(hw2reg_o.stby_cr_ccc_config_rstact_params.rst_action.d);

  // Target Error counting (TE[6:0], Table 43).
  logic [6:0] targ_trx_te;
  logic [6:0] targ_error;

  // The Asynchronous Event Queue also has a queue-specific reset under software control.
  logic async_evt_rst;
  assign async_evt_rst = reg2hw_i.targ_async_evt_control.reset.qe
                       & reg2hw_i.targ_async_evt_control.reset.q;

  // Target core.
  i3c_target #(
    .NumTargets (NumTargets),
    .DataWidth  (DataWidth),
    .FIFODepthW (FIFODepthW)
  ) u_target (
    // Clock and reset for system interface.
    .clk_i                (clk_i),
    .rst_ni               (rst_ni),

    // I3C clock signal from the controller.
    .scl_ni               (targ_scl_buf_n),
    // Reset for transceiver logic.
    .trx_rst_ni           (targ_trx_rst_n),

    // Control inputs.
    .enable_i             (targ_enabled),
    .stby_cr_enabled_i    (stby_cr_enabled),
    .sw_reset_i           (targ_sw_reset),
    .async_evt_rst_i      (async_evt_rst),
    // TODO: Target core logic will need to be aware of reset/enable of transceiver logic.

    // HDR pattern detection.
    .hdr_exit_det_i       (hdr_exit_det),
    .hdr_restart_det_i    (hdr_restart_det),

    // Configuration inputs.
    .reg2hw_i             (reg2hw_i),
    .stby_cr_enable_init_i(stby_cr_en_init),
    .stby_cr_cr_req_send_i(hw2reg_o.stby_cr_control.cr_request_send.d),
    .stby_cr_staddr_i     ({hw2reg_o.stby_cr_device_addr.static_addr_valid.d,
                            hw2reg_o.stby_cr_device_addr.static_addr.d}),
    .stby_cr_dynaddr_i    ({hw2reg_o.stby_cr_device_addr.dynamic_addr_valid.d,
                            hw2reg_o.stby_cr_device_addr.dynamic_addr.d}),
    .stby_cr_dcr_i        (hw2reg_o.stby_cr_device_char.dcr.d),
    .stby_cr_bcr_i        ({hw2reg_o.stby_cr_device_char.bcr_fixed.d,
                            hw2reg_o.stby_cr_device_char.bcr_var.d}),
    .stby_cr_pid_i        ({hw2reg_o.stby_cr_device_char.pid_hi.d, 1'b0,
                           hw2reg_o.stby_cr_device_pid_lo.d}),
    .rstact_i             (i3c_rstact_e'(hw2reg_o.stby_cr_ccc_config_rstact_params.rst_action.d)),
    // Blocked device addresses.
    .addr_blocked_i       (addr_blocked),
    .mask_blocked_i       (mask_blocked),

    // Control outputs.
    .hdr_exit_det_en_o    (hdr_exit_det_en),

    // Bus signals, already synchronized to the IP clock domain.
    .scl_i                (targ_scl_sync),
    .sda_i                (targ_sda_sync),
    // Bus status signals.
    .bus_avail_i          (targ_bus_avail),
    .bus_idle_i           (targ_bus_idle),

    // State information, presented via TTI.
    .dynaddr_de_o         (targ_dynaddr_de),
    .dynaddr_valid_d_o    (targ_dynaddr_valid_d),
    .dynaddr_d_o          (targ_dynaddr_d),
    .virt_targ_det_o      (hw2reg_o.targ_status.rstact_virt_targ_det.d),  // I3C Basic 4.3.7.3.23.2.
    .mwl_de_o             (targ_mwl_de),
    .mrl_de_o             (targ_mrl_de),
    .ibi_de_o             (targ_ibi_de),
    .mwl_d_o              (targ_mwl_d),
    .mrl_d_o              (targ_mrl_d),
    .ibi_d_o              (targ_ibi_d),
    .endis_event_o        (targ_endis_evt),
    .rstact_de_o          (targ_rstact_de),
    .rstact_d_o           (targ_rstact_d),  // I3C Basic Table 38.
    .grp_addr_de_o        (targ_grp_addr_de),
    .grp_targ_de_o        (targ_grp_targ_de),
    .grp_addr_d_o         (targ_grp_addr_d),
    .grp_targ_d_o         (targ_grp_targ_d),
    .act_state_de_o       (targ_act_state_de),
    .act_state_d_o        (targ_act_state_d),
    .endxfer_cand_de_o    (targ_endxfer_cand_de),
    .endxfer_cand_d_o     (targ_endxfer_cand_d),
    .endxfer_de_o         (targ_endxfer_de),
    .endxfer_d_o          (targ_endxfer_d),
    .vend_test_mode_o     (hw2reg_o.targ_status.vtm.d),
    .protocol_error_o     (hw2reg_o.targ_status.protocol_error.d),

    // Interrupts to the TTI.
    .intr_o               (targ_interrupts),

    // Target device descriptions.
    .targ_dev_o           (targ_dev),
    // Group address descriptions.
    .grp_addr_o           (grp_addr),

    // Start request to the transceiver.
    .sreq_sda_od_en_o     (targ_sreq_sda_od_en),
    .sreq_sda_o           (targ_sreq_sda),

    // Status indications from the transceiver.
    .rep_start_det_i      (targ_rep_start_det),
    .stop_det_i           (targ_stop_det),
    .ddr_mode_i           (targ_ddr_mode),

    // Transmission from Virtual Target(s) suspended.
    .suspend_tx_o         (targ_suspend_tx),
    // IBI Transmission suspended.
    .ibi_suspend_tx_o     (hw2reg_o.targ_pio_control.ibi_suspended.de),
    // Clear the Abort status when transmission is resumed.
    .abort_clr_o          (targ_abort_clr),
    .ibi_abort_clr_o      (hw2reg_o.targ_pio_control.ibi_abort.de),

    // Transmission Descriptor access.
    .tx_desc_rready_o     (targ_tx_desc_rready),
    .tx_desc_rvalid_i     (targ_tx_desc_rvalid),
    .tx_desc_rdata_i      (targ_tx_desc_rdata),
    .tx_desc_rused_i      (targ_tx_desc_rused),
    .tx_desc_ravail_i     (targ_tx_desc_ravail),

    // Reception Descriptor access.
    .rx_desc_wvalid_o     (fifo_in[FIFO_RxDTarg].wvalid),
    .rx_desc_wdata_o      (fifo_in[FIFO_RxDTarg].wdata),
    .rx_desc_wready_i     (fifo_out[FIFO_RxDTarg].wready),
    .rx_desc_wused_i      (fifo_state[FIFO_RxDTarg].used),
    .rx_desc_wfull_i      (fifo_state[FIFO_RxDTarg].full),

    // In-Band Interrupt Descriptor access.
    .ibi_desc_rready_o    (fifo_in[FIFO_IBIDTarg].rready),
    .ibi_desc_rvalid_i    (fifo_out[FIFO_IBIDTarg].rvalid),
    .ibi_desc_rdata_i     (fifo_out[FIFO_IBIDTarg].rdata),
    .ibi_desc_ravail_i    (fifo_state[FIFO_IBIDTarg].avail),

    // Buffer reading.
    .buf_rready_o         (targ_buf_rready),
    .buf_rvalid_i         (targ_buf_rvalid),
    .buf_rdata_i          (targ_buf_rdata),
    .buf_rused_i          (targ_buf_rused),
    .buf_ravail_i         (targ_buf_ravail),

    // In-Band Interrupt reading.
    .ibi_rready_o         (fifo_in[FIFO_IBITarg].rready),
    .ibi_rvalid_i         (fifo_out[FIFO_IBITarg].rvalid),
    .ibi_rdata_i          (fifo_out[FIFO_IBITarg].rdata),
    .ibi_rused_i          (fifo_state[FIFO_IBITarg].used),

    // Transmit data to the transceiver, for Private Read transfers.
    .trx_dvalid_o         (targ_trx_dvalid),
    .trx_dready_i         (targ_trx_dready),
    .trx_dreq_o           (targ_trx_dreq),

    // Transmit data for Direct Read CCCs.
    .trx_ctvalid_o        (targ_trx_ctvalid),
    .trx_ctready_i        (targ_trx_ctready),
    .trx_ctreq_o          (targ_trx_ctreq),

    // Arbitration requests to the transceiver.
    .trx_avalid_o         (targ_trx_avalid),
    .trx_aready_i         (targ_trx_aready),
    .trx_areq_o           (targ_trx_areq),

    // Response from the transceiver.
    .trx_rtoggle_i        (targ_trx_rtoggle),
    .trx_rxd_i            (targ_trx_rxd),

    // Buffer writing.
    .buf_wvalid_o         (fifo_in[FIFO_RxTarg].wvalid),
    .buf_wdata_o          (fifo_in[FIFO_RxTarg].wdata),
    .buf_wready_i         (fifo_out[FIFO_RxTarg].wready),
    .buf_wused_i          (fifo_state[FIFO_RxTarg].used),
    .buf_wavail_i         (fifo_state[FIFO_RxTarg].avail),

    // Asynchronous Event Queue.
    .async_wvalid_o       (fifo_in[FIFO_AsyncTarg].wvalid),
    .async_wdata_o        (fifo_in[FIFO_AsyncTarg].wdata),
    .async_wready_i       (fifo_out[FIFO_AsyncTarg].wready),
    .async_empty_i        (fifo_state[FIFO_AsyncTarg].empty),

    // Target Reset Detector request/response.
    .rstdet_req_o         (rstdet_req_o),
    .rstdet_rsp_i         (rstdet_rsp_i),

    // Setting the Standby Controller Dynamic Address.
    .stby_cr_dynaddr_de_o (stby_cr_dynaddr_de),
    .stby_cr_dynaddr_d_o  (stby_cr_dynaddr_d),

    // Broadcast CCCs received in Standby Controller mode.
    .stby_bcst_wvalid_o   (stby_bcst_wvalid),
    .stby_bcst_wdata_o    (stby_bcst_wdata),
    .stby_bcst_wready_i   (stby_bcst_wready),

    // Target Errors (TE6:0, Table 43).
    .trx_te_i             (targ_trx_te),
    .targ_error_o         (targ_error),

    // Data sink status signals.
    .sink_active_o        (hw2reg_o.targ_sink_status.active.d),
    .sink_error_o         (hw2reg_o.targ_sink_status.error.d),

    // Diagnostic visibility into the Target core.
    .fsm_state_o          (hw2reg_o.targ_state_debug.fsm_state.d)
  );

  // Buffer configuration.
  // - a single physical buffer implements a number of logical FIFOs.
  assign fifo_cfg[FIFO_CmdQ].min   = BufAddrW'(reg2hw_i.command_queue_config.min_addr.q);
  assign fifo_cfg[FIFO_CmdQ].max   = BufAddrW'(reg2hw_i.command_queue_config.max_addr.q);
  assign fifo_cfg[FIFO_CmdQ].size  = fifo_size(fifo_cfg[FIFO_CmdQ]);

  assign fifo_cfg[FIFO_RspQ].min   = BufAddrW'(reg2hw_i.response_queue_config.min_addr.q);
  assign fifo_cfg[FIFO_RspQ].max   = BufAddrW'(reg2hw_i.response_queue_config.max_addr.q);
  assign fifo_cfg[FIFO_RspQ].size  = fifo_size(fifo_cfg[FIFO_RspQ]);

  assign fifo_cfg[FIFO_IBIQ].min   = BufAddrW'(reg2hw_i.ibi_config.min_addr.q);
  assign fifo_cfg[FIFO_IBIQ].max   = BufAddrW'(reg2hw_i.ibi_config.max_addr.q);
  assign fifo_cfg[FIFO_IBIQ].size  = fifo_size(fifo_cfg[FIFO_IBIQ]);

  assign fifo_cfg[FIFO_IBIStD].min   = BufAddrW'(reg2hw_i.ibi_stat_config.min_addr.q);
  assign fifo_cfg[FIFO_IBIStD].max   = BufAddrW'(reg2hw_i.ibi_stat_config.max_addr.q);
  assign fifo_cfg[FIFO_IBIStD].size  = fifo_size(fifo_cfg[FIFO_IBIStD]);

  assign fifo_cfg[FIFO_TxBuf].min   = BufAddrW'(reg2hw_i.ctrl_txbuf_config.min_addr.q);
  assign fifo_cfg[FIFO_TxBuf].max   = BufAddrW'(reg2hw_i.ctrl_txbuf_config.max_addr.q);
  assign fifo_cfg[FIFO_TxBuf].size  = fifo_size(fifo_cfg[FIFO_TxBuf]);

  assign fifo_cfg[FIFO_RxBuf].min   = BufAddrW'(reg2hw_i.ctrl_rxbuf_config.min_addr.q);
  assign fifo_cfg[FIFO_RxBuf].max   = BufAddrW'(reg2hw_i.ctrl_rxbuf_config.max_addr.q);
  assign fifo_cfg[FIFO_RxBuf].size  = fifo_size(fifo_cfg[FIFO_RxBuf]);

  assign fifo_cfg[FIFO_IBITarg].min  = BufAddrW'(reg2hw_i.targ_ibi_config.min_addr.q);
  assign fifo_cfg[FIFO_IBITarg].max  = BufAddrW'(reg2hw_i.targ_ibi_config.min_addr.q);
  assign fifo_cfg[FIFO_IBITarg].size = fifo_size(fifo_cfg[FIFO_IBITarg]);

  assign fifo_cfg[FIFO_TxTarg0].min  = BufAddrW'(reg2hw_i.targ0_txbuf_config.min_addr.q);
  assign fifo_cfg[FIFO_TxTarg0].max  = BufAddrW'(reg2hw_i.targ0_txbuf_config.max_addr.q);
  assign fifo_cfg[FIFO_TxTarg0].size = fifo_size(fifo_cfg[FIFO_TxTarg0]);

  assign fifo_cfg[FIFO_TxTarg1].min  = BufAddrW'(reg2hw_i.targ1_txbuf_config.min_addr.q);
  assign fifo_cfg[FIFO_TxTarg1].max  = BufAddrW'(reg2hw_i.targ1_txbuf_config.max_addr.q);
  assign fifo_cfg[FIFO_TxTarg1].size = fifo_size(fifo_cfg[FIFO_TxTarg1]);

  assign fifo_cfg[FIFO_RxTarg].min  = BufAddrW'(reg2hw_i.targ_rxbuf_config.min_addr.q);
  assign fifo_cfg[FIFO_RxTarg].max  = BufAddrW'(reg2hw_i.targ_rxbuf_config.max_addr.q);
  assign fifo_cfg[FIFO_RxTarg].size = fifo_size(fifo_cfg[FIFO_RxTarg]);

  assign fifo_cfg[FIFO_TxDTarg0].min  = BufAddrW'(reg2hw_i.targ0_txdesc_config.min_addr.q);
  assign fifo_cfg[FIFO_TxDTarg0].max  = BufAddrW'(reg2hw_i.targ0_txdesc_config.max_addr.q);
  assign fifo_cfg[FIFO_TxDTarg0].size = fifo_size(fifo_cfg[FIFO_TxDTarg0]);

  assign fifo_cfg[FIFO_TxDTarg1].min  = BufAddrW'(reg2hw_i.targ1_txdesc_config.min_addr.q);
  assign fifo_cfg[FIFO_TxDTarg1].max  = BufAddrW'(reg2hw_i.targ1_txdesc_config.max_addr.q);
  assign fifo_cfg[FIFO_TxDTarg1].size = fifo_size(fifo_cfg[FIFO_TxDTarg1]);

  assign fifo_cfg[FIFO_RxDTarg].min  = BufAddrW'(reg2hw_i.targ_rxdesc_config.min_addr.q);
  assign fifo_cfg[FIFO_RxDTarg].max  = BufAddrW'(reg2hw_i.targ_rxdesc_config.max_addr.q);
  assign fifo_cfg[FIFO_RxDTarg].size = fifo_size(fifo_cfg[FIFO_RxDTarg]);

  assign fifo_cfg[FIFO_IBIDTarg].min  = BufAddrW'(reg2hw_i.targ_ibidesc_config.min_addr.q);
  assign fifo_cfg[FIFO_IBIDTarg].max  = BufAddrW'(reg2hw_i.targ_ibidesc_config.max_addr.q);
  assign fifo_cfg[FIFO_IBIDTarg].size = fifo_size(fifo_cfg[FIFO_IBIDTarg]);

  assign fifo_cfg[FIFO_AsyncTarg].min  = BufAddrW'(reg2hw_i.targ_async_config.min_addr.q);
  assign fifo_cfg[FIFO_AsyncTarg].max  = BufAddrW'(reg2hw_i.targ_async_config.max_addr.q);
  assign fifo_cfg[FIFO_AsyncTarg].size = fifo_size(fifo_cfg[FIFO_AsyncTarg]);

  // FIFO software reset signals.
  // - when first enabling one or more FIFO use cases, `i3c_buffer` needs to initialize pointers.
  wire buffer_clear = (reg2hw_i.buffer_ctrl.clear.qe & reg2hw_i.buffer_ctrl.clear.q) | enabling;
  assign fifo_rst[FIFO_CmdQ]   = (reg2hw_i.reset_control.cmd_queue_rst.qe &
                                  reg2hw_i.reset_control.cmd_queue_rst.q) | buffer_clear;
  assign fifo_rst[FIFO_RspQ]   = (reg2hw_i.reset_control.resp_queue_rst.qe &
                                  reg2hw_i.reset_control.resp_queue_rst.q) | buffer_clear;
  assign fifo_rst[FIFO_IBIQ]   = (reg2hw_i.reset_control.ibi_queue_rst.qe &
                                  reg2hw_i.reset_control.ibi_queue_rst.q) | buffer_clear;
  assign fifo_rst[FIFO_IBIStD] = fifo_rst[FIFO_IBIQ];
  assign fifo_rst[FIFO_TxBuf]  = (reg2hw_i.reset_control.tx_fifo_rst.qe &
                                  reg2hw_i.reset_control.tx_fifo_rst.q) | buffer_clear;
  assign fifo_rst[FIFO_RxBuf]  = (reg2hw_i.reset_control.rx_fifo_rst.qe &
                                  reg2hw_i.reset_control.rx_fifo_rst.q) | buffer_clear;

  assign fifo_rst[FIFO_TxTarg0]   = buffer_clear;
  assign fifo_rst[FIFO_TxTarg1]   = buffer_clear;
  assign fifo_rst[FIFO_RxTarg]    = buffer_clear;
  assign fifo_rst[FIFO_IBITarg]   = buffer_clear;
  assign fifo_rst[FIFO_RxDTarg]   = buffer_clear;
  assign fifo_rst[FIFO_TxDTarg0]  = buffer_clear;
  assign fifo_rst[FIFO_TxDTarg1]  = buffer_clear;
  assign fifo_rst[FIFO_IBIDTarg]  = buffer_clear;
  assign fifo_rst[FIFO_AsyncTarg] = buffer_clear | async_evt_rst;

  // Diagnostic information about the virtual FIFOs is presented in the register API.
  //
  // Report FIFO write pointers in registers.
  assign hw2reg_o.command_queue_state.wptr.d  = fifo_state[FIFO_CmdQ].wptr;
  assign hw2reg_o.response_queue_state.wptr.d = fifo_state[FIFO_RspQ].wptr;
  assign hw2reg_o.ibi_state.wptr.d            = fifo_state[FIFO_IBIQ].wptr;
  assign hw2reg_o.ibi_stat_state.wptr.d       = fifo_state[FIFO_IBIStD].wptr;
  assign hw2reg_o.ctrl_txbuf_state.wptr.d     = fifo_state[FIFO_TxBuf].wptr;
  assign hw2reg_o.ctrl_rxbuf_state.wptr.d     = fifo_state[FIFO_RxBuf].wptr;
  assign hw2reg_o.targ0_txbuf_state.wptr.d    = fifo_state[FIFO_TxTarg0].wptr;
  assign hw2reg_o.targ1_txbuf_state.wptr.d    = fifo_state[FIFO_TxTarg1].wptr;
  assign hw2reg_o.targ_rxbuf_state.wptr.d     = fifo_state[FIFO_RxTarg].wptr;
  assign hw2reg_o.targ_ibi_state.wptr.d       = fifo_state[FIFO_IBITarg].wptr;
  assign hw2reg_o.targ0_txdesc_state.wptr.d   = fifo_state[FIFO_TxDTarg0].wptr;
  assign hw2reg_o.targ1_txdesc_state.wptr.d   = fifo_state[FIFO_TxDTarg1].wptr;
  assign hw2reg_o.targ_rxdesc_state.wptr.d    = fifo_state[FIFO_RxDTarg].wptr;
  assign hw2reg_o.targ_ibidesc_state.wptr.d   = fifo_state[FIFO_IBIDTarg].wptr;
  assign hw2reg_o.targ_async_state.wptr.d     = fifo_state[FIFO_AsyncTarg].wptr;
  // Report FIFO read pointers in registers.
  assign hw2reg_o.command_queue_state.rptr.d  = fifo_state[FIFO_CmdQ].rptr;
  assign hw2reg_o.response_queue_state.rptr.d = fifo_state[FIFO_RspQ].rptr;
  assign hw2reg_o.ibi_state.rptr.d            = fifo_state[FIFO_IBIQ].rptr;
  assign hw2reg_o.ibi_stat_state.rptr.d       = fifo_state[FIFO_IBIStD].rptr;
  assign hw2reg_o.ctrl_txbuf_state.rptr.d     = fifo_state[FIFO_TxBuf].rptr;
  assign hw2reg_o.ctrl_rxbuf_state.rptr.d     = fifo_state[FIFO_RxBuf].rptr;
  assign hw2reg_o.targ0_txbuf_state.rptr.d    = fifo_state[FIFO_TxTarg0].rptr;
  assign hw2reg_o.targ1_txbuf_state.rptr.d    = fifo_state[FIFO_TxTarg1].rptr;
  assign hw2reg_o.targ_rxbuf_state.rptr.d     = fifo_state[FIFO_RxTarg].rptr;
  assign hw2reg_o.targ_ibi_state.rptr.d       = fifo_state[FIFO_IBITarg].rptr;
  assign hw2reg_o.targ0_txdesc_state.rptr.d   = fifo_state[FIFO_TxDTarg0].rptr;
  assign hw2reg_o.targ1_txdesc_state.rptr.d   = fifo_state[FIFO_TxDTarg1].rptr;
  assign hw2reg_o.targ_rxdesc_state.rptr.d    = fifo_state[FIFO_RxDTarg].rptr;
  assign hw2reg_o.targ_ibidesc_state.rptr.d   = fifo_state[FIFO_IBIDTarg].rptr;
  assign hw2reg_o.targ_async_state.rptr.d     = fifo_state[FIFO_AsyncTarg].rptr;
  // Report whether prefetched data is available.
  assign hw2reg_o.command_queue_state.pre.d   = fifo_state[FIFO_CmdQ].pre;
  assign hw2reg_o.response_queue_state.pre.d  = fifo_state[FIFO_RspQ].pre;
  assign hw2reg_o.ibi_state.pre.d             = fifo_state[FIFO_IBIQ].pre;
  assign hw2reg_o.ibi_stat_state.pre.d        = fifo_state[FIFO_IBIStD].pre;
  assign hw2reg_o.ctrl_txbuf_state.pre.d      = fifo_state[FIFO_TxBuf].pre;
  assign hw2reg_o.ctrl_rxbuf_state.pre.d      = fifo_state[FIFO_RxBuf].pre;
  assign hw2reg_o.targ0_txbuf_state.pre.d     = fifo_state[FIFO_TxTarg0].pre;
  assign hw2reg_o.targ1_txbuf_state.pre.d     = fifo_state[FIFO_TxTarg1].pre;
  assign hw2reg_o.targ_rxbuf_state.pre.d      = fifo_state[FIFO_RxTarg].pre;
  assign hw2reg_o.targ_ibi_state.pre.d        = fifo_state[FIFO_IBITarg].pre;
  assign hw2reg_o.targ0_txdesc_state.pre.d    = fifo_state[FIFO_TxDTarg0].pre;
  assign hw2reg_o.targ1_txdesc_state.pre.d    = fifo_state[FIFO_TxDTarg1].pre;
  assign hw2reg_o.targ_rxdesc_state.pre.d     = fifo_state[FIFO_RxDTarg].pre;
  assign hw2reg_o.targ_ibidesc_state.pre.d    = fifo_state[FIFO_IBIDTarg].pre;
  assign hw2reg_o.targ_async_state.pre.d      = fifo_state[FIFO_AsyncTarg].pre;
  // FIFO full indicators.
  assign hw2reg_o.command_queue_state.full.d  = fifo_state[FIFO_CmdQ].full;
  assign hw2reg_o.response_queue_state.full.d = fifo_state[FIFO_RspQ].full;
  assign hw2reg_o.ibi_state.full.d            = fifo_state[FIFO_IBIQ].full;
  assign hw2reg_o.ibi_stat_state.full.d       = fifo_state[FIFO_IBIStD].full;
  assign hw2reg_o.ctrl_txbuf_state.full.d     = fifo_state[FIFO_TxBuf].full;
  assign hw2reg_o.ctrl_rxbuf_state.full.d     = fifo_state[FIFO_RxBuf].full;
  assign hw2reg_o.targ0_txbuf_state.full.d    = fifo_state[FIFO_TxTarg0].full;
  assign hw2reg_o.targ1_txbuf_state.full.d    = fifo_state[FIFO_TxTarg1].full;
  assign hw2reg_o.targ_rxbuf_state.full.d     = fifo_state[FIFO_RxTarg].full;
  assign hw2reg_o.targ_ibi_state.full.d       = fifo_state[FIFO_IBITarg].full;
  assign hw2reg_o.targ0_txdesc_state.full.d   = fifo_state[FIFO_TxDTarg0].full;
  assign hw2reg_o.targ1_txdesc_state.full.d   = fifo_state[FIFO_TxDTarg1].full;
  assign hw2reg_o.targ_rxdesc_state.full.d    = fifo_state[FIFO_RxDTarg].full;
  assign hw2reg_o.targ_ibidesc_state.full.d   = fifo_state[FIFO_IBIDTarg].full;
  assign hw2reg_o.targ_async_state.full.d     = fifo_state[FIFO_AsyncTarg].full;

  // The IBI Queue as presented at the HCI is actually implemented as two FIFOs physically,
  // interleaving the IBI Status Descriptors amongst the IBI data words that they describe.
  logic ibi_empty, ibi_avail;
  assign ibi_empty = ibi_status_desc ? fifo_state[FIFO_IBIStD].empty : fifo_state[FIFO_IBIQ].empty;
  assign ibi_avail = ibi_status_desc ? fifo_out[FIFO_IBIStD].rvalid  : fifo_out[FIFO_IBIQ].rvalid;
  assign ibi_rdata = ibi_status_desc ? fifo_out[FIFO_IBIStD].rdata   : fifo_out[FIFO_IBIQ].rdata;
  assign ibi_read  = ibi_status_desc ? fifo_in[FIFO_IBIStD].rready   : fifo_in[FIFO_IBIQ].rready;

  // Diagnostic indicator reporting invalid queue access; implies a driver error.
  logic hciq_access_err, ttiq_access_err;
  assign hw2reg_o.buffer_status.hciq_err.de = hciq_access_err;
  assign hw2reg_o.buffer_status.hciq_err.d  = 1'b1;
  assign hw2reg_o.buffer_status.ttiq_err.de = ttiq_access_err;
  assign hw2reg_o.buffer_status.ttiq_err.d  = 1'b1;

  logic                 hci_wvalid[4], tti_wvalid[13];
  logic                 hci_rready[4], tti_rready[13];
  logic [DataWidth-1:0] hci_wdata,     tti_wdata;
  always_comb begin
    fifo_in[FIFO_CmdQ].wvalid      = hci_wvalid[0];
    fifo_in[FIFO_TxBuf].wvalid     = hci_wvalid[2];

    fifo_in[FIFO_IBIDTarg].wvalid  = tti_wvalid[2];
    fifo_in[FIFO_IBITarg].wvalid   = tti_wvalid[3];
    fifo_in[FIFO_TxDTarg0].wvalid  = tti_wvalid[5];
    fifo_in[FIFO_TxDTarg1].wvalid  = tti_wvalid[6];
    fifo_in[FIFO_TxTarg0].wvalid   = tti_wvalid[9];
    fifo_in[FIFO_TxTarg1].wvalid   = tti_wvalid[10];

    fifo_in[FIFO_CmdQ].wdata       = hci_wdata;
    fifo_in[FIFO_TxBuf].wdata      = hci_wdata;

    fifo_in[FIFO_IBIDTarg].wdata   = tti_wdata;
    fifo_in[FIFO_IBITarg].wdata    = tti_wdata;
    fifo_in[FIFO_TxDTarg0].wdata   = tti_wdata;
    fifo_in[FIFO_TxDTarg1].wdata   = tti_wdata;
    fifo_in[FIFO_TxTarg0].wdata    = tti_wdata;
    fifo_in[FIFO_TxTarg1].wdata    = tti_wdata;

    fifo_in[FIFO_RspQ].rready      = hci_rready[1];
    fifo_in[FIFO_RxBuf].rready     = hci_rready[2];
    // IBI_PORT is implemented as two queues, one carrying the IBI payload data and the other
    // holding IBI Status Descriptors.
    fifo_in[FIFO_IBIQ].rready      = hci_rready[3] & !ibi_status_desc;
    fifo_in[FIFO_IBIStD].rready    = hci_rready[3] &  ibi_status_desc;

    fifo_in[FIFO_RxDTarg].rready   = tti_rready[0];
    fifo_in[FIFO_RxTarg].rready    = tti_rready[1];
    fifo_in[FIFO_AsyncTarg].rready = tti_rready[4];
  end

  // Host Controller Interface queues.
  i3c_queues #(
    .NumQueues  (4),
    .DW         (DataWidth),
    .SupportTx  (4'b0101),
    .SupportRx  (4'b1110)
  ) u_hci_queues (
    // Clock and reset.
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    // Single SRAM interface.
    .req_i        (bufq_req_i[TL_HCI]),
    .gnt_o        (bufq_gnt_o[TL_HCI]),
    .we_i         (bufq_we_i[TL_HCI]),
    .addr_i       (bufq_addr_i[TL_HCI][1:0]),
    .wdata_i      (bufq_wdata_i[TL_HCI]),
    .rvalid_o     (bufq_rvalid_o[TL_HCI]),
    .rdata_o      (bufq_rdata_o[TL_HCI]),

    // Writes to logical queues.
    .buf_wready_i ({fifo_out[FIFO_CmdQ].wready,
                    fifo_out[FIFO_RspQ].wready,
                    fifo_out[FIFO_TxBuf].wready,
                    fifo_out[FIFO_IBIQ].wready}),
    .buf_full_i   ({fifo_state[FIFO_CmdQ].full,
                    fifo_state[FIFO_RspQ].full,
                    fifo_state[FIFO_TxBuf].full,
                    fifo_state[FIFO_IBIQ].full}),
    .buf_wvalid_o (hci_wvalid),
    .buf_wdata_o  (hci_wdata),

    // Reads from logical queues.
    .buf_rvalid_i ({fifo_out[FIFO_CmdQ].rvalid,
                    fifo_out[FIFO_RspQ].rvalid,
                    fifo_out[FIFO_RxBuf].rvalid,
                    ibi_avail}),
    .buf_rdata_i  ({fifo_out[FIFO_CmdQ].rdata,
                    fifo_out[FIFO_RspQ].rdata,
                    fifo_out[FIFO_RxBuf].rdata,
                    ibi_rdata}),
    .buf_empty_i  ({fifo_state[FIFO_CmdQ].empty,
                    fifo_state[FIFO_RspQ].empty,
                    fifo_state[FIFO_RxBuf].empty,
                    ibi_empty}),
    .buf_rready_o (hci_rready),

    // Diagnostic error indicator.
    .err_o        (hciq_access_err)
  );

  // Target Transaction Interface queues.
  i3c_queues #(
    .NumQueues  (13),
    .DW         (DataWidth),
    .SupportTx  (13'b1111111101100),
    .SupportRx  (13'b0000000010011)
  ) u_tti_queues (
    // Clock and reset.
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    // Single SRAM interface.
    .req_i        (bufq_req_i[TL_TTI]),
    .gnt_o        (bufq_gnt_o[TL_TTI]),
    .we_i         (bufq_we_i[TL_TTI]),
    .addr_i       (bufq_addr_i[TL_TTI]),
    .wdata_i      (bufq_wdata_i[TL_TTI]),
    .rvalid_o     (bufq_rvalid_o[TL_TTI]),
    .rdata_o      (bufq_rdata_o[TL_TTI]),

    // Writes to logical queues.
    .buf_wready_i ({fifo_out[FIFO_RxDTarg].wready,
                    fifo_out[FIFO_RxTarg].wready,
                    fifo_out[FIFO_IBIDTarg].wready,
                    fifo_out[FIFO_IBITarg].wready,
                    fifo_out[FIFO_AsyncTarg].wready,
                    fifo_out[FIFO_TxDTarg0].wready,
                    fifo_out[FIFO_TxDTarg1].wready,
                    1'b1,  // Not implemented.
                    1'b1,
                    fifo_out[FIFO_TxTarg0].wready,
                    fifo_out[FIFO_TxTarg1].wready,
                    1'b1,
                    1'b1}),
    .buf_full_i   ({fifo_state[FIFO_RxDTarg].full,
                    fifo_state[FIFO_RxTarg].full,
                    fifo_state[FIFO_IBIDTarg].full,
                    fifo_state[FIFO_IBITarg].full,
                    fifo_state[FIFO_AsyncTarg].full,
                    fifo_state[FIFO_TxDTarg0].full,
                    fifo_state[FIFO_TxDTarg1].full,
                    1'b0,  // Not implemented.
                    1'b0,
                    fifo_state[FIFO_TxTarg0].full,
                    fifo_state[FIFO_TxTarg1].full,
                    1'b0,  // Not implemented.
                    1'b0}),
    .buf_wvalid_o (tti_wvalid),
    .buf_wdata_o  (tti_wdata),

    // Reads from logical queues.
    .buf_rvalid_i ({fifo_out[FIFO_RxDTarg].rvalid,
                    fifo_out[FIFO_RxTarg].rvalid,
                    fifo_out[FIFO_IBIDTarg].rvalid,
                    fifo_out[FIFO_IBITarg].rvalid,
                    fifo_out[FIFO_AsyncTarg].rvalid,
                    fifo_out[FIFO_TxDTarg0].rvalid,
                    fifo_out[FIFO_TxDTarg1].rvalid,
                    1'b0,  // Not implemented.
                    1'b0,
                    fifo_out[FIFO_TxTarg0].rvalid,
                    fifo_out[FIFO_TxTarg1].rvalid,
                    1'b0,  // Not implemented.
                    1'b0}),
    .buf_rdata_i  ({fifo_out[FIFO_RxDTarg].rdata,
                    fifo_out[FIFO_RxTarg].rdata,
                    fifo_out[FIFO_IBIDTarg].rdata,
                    fifo_out[FIFO_IBITarg].rdata,
                    fifo_out[FIFO_AsyncTarg].rdata,
                    fifo_out[FIFO_TxDTarg0].rdata,
                    fifo_out[FIFO_TxDTarg1].rdata,
                    DataWidth'(0),  // Not implemented.
                    DataWidth'(0),
                    fifo_out[FIFO_TxTarg0].rdata,
                    fifo_out[FIFO_TxTarg1].rdata,
                    DataWidth'(0),  // Not implemented.
                    DataWidth'(0)}),
    .buf_empty_i  ({fifo_state[FIFO_RxDTarg].empty,
                    fifo_state[FIFO_RxTarg].empty,
                    fifo_state[FIFO_IBIDTarg].empty,
                    fifo_state[FIFO_IBITarg].empty,
                    fifo_state[FIFO_AsyncTarg].empty,
                    fifo_state[FIFO_TxDTarg0].empty,
                    fifo_state[FIFO_TxDTarg1].empty,
                    1'b1,  // Not implemented.
                    1'b1,
                    fifo_state[FIFO_TxTarg0].empty,
                    fifo_state[FIFO_TxTarg1].empty,
                    1'b1,  // Not implemented.
                    1'b1}),
    .buf_rready_o (tti_rready),

    // Diagnostic error indicator.
    .err_o        (ttiq_access_err)
  );

  // When software has direct access to the entire message buffer we can map at most 2KiB into
  // the address space, so collect any extra address bits from the register.
  logic [BufAddrW-1:0] sw_buf_addr;
  logic [1:0] sw_addr_hi_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) sw_addr_hi_q <= I3C_BUFFER_CTRL_SW_ADDR_HI_RESVAL;
    else if (reg2hw_i.buffer_ctrl.sw_addr_hi.qe) sw_addr_hi_q <= reg2hw_i.buffer_ctrl.sw_addr_hi.q;
  end
  assign hw2reg_o.buffer_ctrl.sw_addr_hi.d = sw_addr_hi_q;
  assign sw_buf_addr = BufAddrW'({sw_addr_hi_q, sw_buf_addr_i});

  // Data buffer for transmission and reception.
  i3c_buffer #(
    .BufAddrW  (BufAddrW),
    .DataWidth (DataWidth),
    .NumFIFOs  (FIFO_Count),
    // These FIFOs are involved in the transmission of data over the I3C bus, which means that
    // read prefetching must be prioritized over writing.
    .DirTx     (FIFO_Count'((1 << FIFO_CmdQ)    | (1 << FIFO_TxBuf)    |
                            (1 << FIFO_TxTarg0) | (1 << FIFO_TxDTarg0) |
                            (1 << FIFO_TxTarg1) | (1 << FIFO_TxDTarg1) |
                            (1 << FIFO_IBITarg) | (1 << FIFO_IBIDTarg)))
  ) u_buf (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),

    // Synchronous FIFO resets.
    .sw_reset_i         (fifo_rst),

    // FIFO configuration.
    .cfg_i              (fifo_cfg),
    // FIFO input signals.
    .in_i               (fifo_in),
    // FIFO output signals.
    .out_o              (fifo_out),
    // Current IFFO state.
    .state_o            (fifo_state),

    // Direct software interface to buffer.
    .sw_buf_req_i       (sw_buf_req_i),
    .sw_buf_gnt_o       (sw_buf_gnt_o),
    .sw_buf_we_i        (sw_buf_we_i),
    .sw_buf_addr_i      (sw_buf_addr),
    .sw_buf_wdata_i     (sw_buf_wdata_i),
    .sw_buf_rvalid_o    (sw_buf_rvalid_o),
    .sw_buf_rerror_o    (sw_buf_rerror_o),
    .sw_buf_rdata_o     (sw_buf_rdata_o),

    // DFT-related signals.
    .ram_cfg_i          (ram_cfg_i),
    .ram_cfg_rsp_o      (ram_cfg_rsp_o)
  );

  // Controller Transceiver.
  i3c_controller_trx #(
    .ClkFreq      (ClkFreq),
    .NumSDALanes  (NumSDALanes),
    .TmCycW       (TmCycW)
  ) u_ctrl_trx (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),

    // Control inputs.
    .enable_i         (ctrl_enabled),
    .sw_reset_i       (ctrl_sw_reset),
    .hotjoin_ctrl_i   (reg2hw_i.hc_control.hot_join_ctrl.q),

    // Blocked addresses.
    .addr_blocked_i   (addr_blocked),
    .mask_blocked_i   (mask_blocked),

    // Start request to the Controller core.
    .trx_sreq_o       (ctrl_trx_sreq),

    // Request from the Controller core.
    .trx_dvalid_i     (ctrl_trx_dvalid),
    .trx_dready_o     (ctrl_trx_dready),
    .trx_dreq_i       (ctrl_trx_dreq),

    // Arbitration requests to the Controller core.
    // - IBI, Hot-Join, Controller Handoff.
    .trx_avalid_o     (ctrl_trx_avalid),
    .trx_arb_o        (ctrl_trx_arb),
    .trx_aready_i     (ctrl_trx_aready),
    .trx_arb_nack_i   (ctrl_trx_arb_nack),

    // Read data from the transceiver.
    .trx_rdvalid_o    (ctrl_trx_rdvalid),
    .trx_rdata_o      (ctrl_trx_rdata),

    // Response to controller core.
    .trx_rvalid_o     (ctrl_trx_rvalid),
    .trx_rready_i     (ctrl_trx_rready),
    .trx_rsp_o        (ctrl_trx_rsp),

    // Timing parameters.
    .tcas_i           (reg2hw_i.ctrl_time0.tcas_div2.q),
    .tcbp_i           (reg2hw_i.ctrl_time0.tcbp_div2.q),

    // Start request signaling from Targets.
    .sreq_sda_i       (ctrl_sda_sync | !ctrl_bus_avail),

    // I3C I/O signaling.
    .sda_i            (ctrl_sda_buf),
    .bus_drv_o        (ctrl_bus_drv_o),

    // Pull-up enables.
    .scl_pu_en_o      (ctrl_scl_pu_en_o),
    .sda_pu_en_o      (ctrl_sda_pu_en_o),

    // Debug status information.
    .bcl_tfr_status_o ({hw2reg_o.present_state_debug.bcl_tfr_status.d})
  );

  // Target Transceiver.
  i3c_target_trx #(
    .NumTargets   (NumTargets),
    .NumSDALanes  (NumSDALanes)
  ) u_targ_trx (
    // No free-running clock from the IP block code; driven by SCL.
    .rst_ni             (targ_trx_rst_n),

    // Target device descriptions.
    // - quasi-static signals
    .targ_dev_i         (targ_dev),
    // Group address descriptions.
    .grp_addr_i         (grp_addr),
    // Blocked addresses.
    .addr_blocked_i     (addr_blocked),
    .mask_blocked_i     (mask_blocked),

    // Transmit data for Private Read transfers, from the Target core.
    .trx_dvalid_i       (targ_trx_dvalid),
    .trx_dready_o       (targ_trx_dready),
    .trx_dreq_i         (targ_trx_dreq),

    // Transmit data for Direct Read CCCs.
    .trx_ctvalid_i      (targ_trx_ctvalid),
    .trx_ctready_o      (targ_trx_ctready),
    .trx_ctreq_i        (targ_trx_ctreq),

    // Arbitration requests to the transceiver.
    .trx_avalid_i       (targ_trx_avalid),
    .trx_aready_o       (targ_trx_aready),
    .trx_areq_i         (targ_trx_areq),

    // Received data, to the Target core.
    .trx_rtoggle_o      (targ_trx_rtoggle),
    .trx_rxd_o          (targ_trx_rxd),

    // Status indications to the Target core.
    .rep_start_det_o    (targ_rep_start_det),
    .stop_det_o         (targ_stop_det),
    .ddr_mode_o         (targ_ddr_mode),

    // Start requests from the Target core.
    .sreq_sda_od_en_i   (targ_sreq_sda_od_en),
    .sreq_sda_i         (targ_sreq_sda),

    // HDR pattern detection.
    .hdr_exit_det_i     (hdr_exit_det),
    .hdr_restart_det_i  (hdr_restart_det),

    // I3C I/O signaling.
    .scl_i              (targ_scl_buf),
    .scl_ni             (targ_scl_buf_n),
    .sda0_clk_i         (targ_sda0_clk),
    .sda0_clk_ni        (targ_sda0_clk_n),
    .sda_i              (targ_sda_buf),
    .bus_drv_o          (targ_bus_drv_o),

    // Diagnostic visibility into Target transceiver state, bus mode and Target Errors.
    .trx_state_o        (targ_trx_state),
    .bus_mode_o         (targ_bus_mode),
    .te_o               (targ_trx_te),

    // DFT-related controls.
    .scanmode_i         (scanmode)
  );

  // Interval timers driven by the IP block, reporting on timed events related to bus activity or
  // inactivity.
  i3c_timers #(
    .ClkFreq    (ClkFreq),
    .NumTimers  (7)
  ) u_timers (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    // For each timer, the minimum interval to be measured is specified in microseconds,
    // allocating 16 bits to each timer in turn.
    .tm_int_i     ({       reg2hw_i.int_time0.dead_bus.q,
                    12'b0, reg2hw_i.int_time0.ctrl_bus_avail.q,
                    4'b0,  reg2hw_i.int_time0.read_stalled.q,
                    12'b0, reg2hw_i.int_time1.targ_bus_avail.q,
                    12'b0, reg2hw_i.int_time1.targ_trx_rst.q,
                    4'b0,  reg2hw_i.int_time1.te0_recov.q,
                    4'b0,  reg2hw_i.int_time1.targ_bus_idle.q}),

    // Resets for interval timers.
    .tm_resets_i  ({rst_dead_bus,
                    ctrl_bus_active,
                    rst_read_stalled,
                    targ_rst_bus_avail,
                    targ_reset_trx,
                    targ_bus_active,
                    targ_bus_active}),
    // 'Time interval elapsed' signals.
    .tm_elapsed_o ({dead_bus,
                    ctrl_bus_avail,
                    read_stalled,
                    targ_bus_avail,
                    targ_trx_rst_n,
                    te0_recov,
                    targ_bus_idle})
  );

  // I3C pattern detector:
  // - HDR Exit, HDR Restart.
  i3c_patt_detector u_patt_det (
    // No free-running clock from the IP block code; driven by SCL.
    .rst_ni             (rst_ni),

    // I3C I/O signaling.
    .scl_i              (targ_scl_buf),
    .sda_clk_i          (targ_sda0_clk),
    .sda_clk_ni         (targ_sda0_clk_n),

    // Control inputs.
    .hdr_exit_det_en_i  (hdr_exit_det_en),

    // HDR pattern detection.
    .hdr_exit_det_o     (hdr_exit_det),
    .hdr_restart_det_o  (hdr_restart_det)
  );

  // IP block information.
  assign hw2reg_o.info.buf_dword_max.d = BufWords      - 1;  // Index of final DWORD.
  assign hw2reg_o.info.dct_entry_max.d = NumDCTEntries - 1;  // Index of final entry.
  assign hw2reg_o.info.dat_entry_max.d = NumDATEntries - 1;
  assign hw2reg_o.info.version.d       = IPVersion;
  assign hw2reg_o.info.revision.d      = IPRevision;
  // Controller and Target 'present' indications; neither can presently be unconfigured.
  assign hw2reg_o.ctrl_status.d = 1'b1;
  assign hw2reg_o.targ_status.present.d = 1'b1;

  // Controller and Target error counting.
  // - CE[3:0] (Table 44), DBR, TE[6:0] (Table 43).
  i3c_counters #(
    .Counters(12),
    .CntW(4)
  ) u_error_cnts (
    // Clock and reset.
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),

    // Input events (count rising edges).
    .event_i    ({ctrl_error, dead_bus, targ_error}),

    // Current counter values.
    .cnt_q_i    ({reg2hw_i.ctrl_error.ce3.q, reg2hw_i.ctrl_error.ce2.q,
                  reg2hw_i.ctrl_error.ce1.q, reg2hw_i.ctrl_error.ce0.q,
                  reg2hw_i.targ_error.dbr.q, reg2hw_i.targ_error.te6.q,
                  reg2hw_i.targ_error.te5.q, reg2hw_i.targ_error.te4.q,
                  reg2hw_i.targ_error.te3.q, reg2hw_i.targ_error.te2.q,
                  reg2hw_i.targ_error.te1.q, reg2hw_i.targ_error.te0.q}),
    // Write strobes to counters.
    .cnt_de_o   ({hw2reg_o.ctrl_error.ce3.de, hw2reg_o.ctrl_error.ce2.de,
                  hw2reg_o.ctrl_error.ce1.de, hw2reg_o.ctrl_error.ce0.de,
                  hw2reg_o.targ_error.dbr.de, hw2reg_o.targ_error.te6.de,
                  hw2reg_o.targ_error.te5.de, hw2reg_o.targ_error.te4.de,
                  hw2reg_o.targ_error.te3.de, hw2reg_o.targ_error.te2.de,
                  hw2reg_o.targ_error.te1.de, hw2reg_o.targ_error.te0.de}),
    // New counter values, saturated.
    .cnt_d_o    ({hw2reg_o.ctrl_error.ce3.d, hw2reg_o.ctrl_error.ce2.d,
                  hw2reg_o.ctrl_error.ce1.d, hw2reg_o.ctrl_error.ce0.d,
                  hw2reg_o.targ_error.dbr.d, hw2reg_o.targ_error.te6.d,
                  hw2reg_o.targ_error.te5.d, hw2reg_o.targ_error.te4.d,
                  hw2reg_o.targ_error.te3.d, hw2reg_o.targ_error.te2.d,
                  hw2reg_o.targ_error.te1.d, hw2reg_o.targ_error.te0.d})
  );

  // Main HCI interrupt; asserted when any HCI interrupt is asserted.
  // TODO: Consider whether perhaps these three should be cleaved?
  logic intr_hc, intr_pio, intr_stby_cr;
  prim_intr_hw #(.IntrT("Status"), .FlopOutput(1)) u_intr_hci (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),

    .event_intr_i           (intr_hc | intr_pio | intr_stby_cr),

    .reg2hw_intr_enable_q_i (reg2hw_i.intr_enable.hci.q),
    .reg2hw_intr_test_q_i   (reg2hw_i.intr_test.hci.q),
    .reg2hw_intr_test_qe_i  (reg2hw_i.intr_test.hci.qe),
    .reg2hw_intr_state_q_i  (reg2hw_i.intr_state.hci.q),
    .hw2reg_intr_state_de_o (hw2reg_o.intr_state.hci.de),
    .hw2reg_intr_state_d_o  (hw2reg_o.intr_state.hci.d),

    .intr_o                 (intr_hci_o)
  );

  // Main Target-side interrupt.
  logic intr_targ;
  prim_intr_hw #(.IntrT("Status"), .FlopOutput(1)) u_intr_targ (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),

    .event_intr_i           (intr_targ),

    .reg2hw_intr_enable_q_i (reg2hw_i.intr_enable.targ.q),
    .reg2hw_intr_test_q_i   (reg2hw_i.intr_test.targ.q),
    .reg2hw_intr_test_qe_i  (reg2hw_i.intr_test.targ.qe),
    .reg2hw_intr_state_q_i  (reg2hw_i.intr_state.targ.q),
    .hw2reg_intr_state_de_o (hw2reg_o.intr_state.targ.de),
    .hw2reg_intr_state_d_o  (hw2reg_o.intr_state.targ.d),

    .intr_o                 (intr_targ_o)
  );

  // General Host Controller interrupts.
  i3c_intr #(.Width($bits(i3c_hc_intr_t)), .EdgeTrig('0)) u_hc_intr (  // TODO: Set interrupt types.
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    .event_i      (hc_interrupts),

    .status_en_i  ({reg2hw_i.intr_status_enable.sched_cmd_missed_tick_stat_en.q,
                    reg2hw_i.intr_status_enable.hc_err_cmd_seq_timeout_stat_en.q,
                    reg2hw_i.intr_status_enable.hc_warn_cmd_seq_stall_stat_en.q,
                    reg2hw_i.intr_status_enable.hc_seq_cancel_stat_en.q,
                    reg2hw_i.intr_status_enable.hc_internal_err_stat_en.q}),
    .status_de_o  ({hw2reg_o.intr_status.sched_cmd_missed_tick_stat.de,
                    hw2reg_o.intr_status.hc_err_cmd_seq_timeout_stat.de,
                    hw2reg_o.intr_status.hc_warn_cmd_seq_stall_stat.de,
                    hw2reg_o.intr_status.hc_seq_cancel_stat.de,
                    hw2reg_o.intr_status.hc_internal_err_stat.de}),
    .status_d_o   ({hw2reg_o.intr_status.sched_cmd_missed_tick_stat.d,
                     hw2reg_o.intr_status.hc_err_cmd_seq_timeout_stat.d,
                    hw2reg_o.intr_status.hc_warn_cmd_seq_stall_stat.d,
                    hw2reg_o.intr_status.hc_seq_cancel_stat.d,
                    hw2reg_o.intr_status.hc_internal_err_stat.d}),
    .force_i      ({reg2hw_i.intr_force.sched_cmd_missed_tick_force.qe &
                    reg2hw_i.intr_force.sched_cmd_missed_tick_force.q,
                    reg2hw_i.intr_force.hc_err_cmd_seq_timeout_force.qe &
                    reg2hw_i.intr_force.hc_err_cmd_seq_timeout_force.q,
                    reg2hw_i.intr_force.hc_warn_cmd_seq_stall_force.qe &
                    reg2hw_i.intr_force.hc_warn_cmd_seq_stall_force.q,
                    reg2hw_i.intr_force.hc_seq_cancel_force.qe &
                    reg2hw_i.intr_force.hc_seq_cancel_force.q,
                    reg2hw_i.intr_force.hc_internal_err_force.qe &
                    reg2hw_i.intr_force.hc_internal_err_force.q}),
    .status_i     ({reg2hw_i.intr_status.sched_cmd_missed_tick_stat.q,
                    reg2hw_i.intr_status.hc_err_cmd_seq_timeout_stat.q,
                    reg2hw_i.intr_status.hc_warn_cmd_seq_stall_stat.q,
                    reg2hw_i.intr_status.hc_seq_cancel_stat.q,
                    reg2hw_i.intr_status.hc_internal_err_stat.q}),
    .signal_en_i  ({reg2hw_i.intr_signal_enable.sched_cmd_missed_tick_signal_en.q,
                    reg2hw_i.intr_signal_enable.hc_err_cmd_seq_timeout_signal_en.q,
                    reg2hw_i.intr_signal_enable.hc_warn_cmd_seq_stall_signal_en.q,
                    reg2hw_i.intr_signal_enable.hc_seq_cancel_signal_en.q,
                    reg2hw_i.intr_signal_enable.hc_internal_err_signal_en.q}),

    .intr_o       (intr_hc)
  );

  // PIO interrupts.
  // TODO: Set interrupt types.
  i3c_intr #(.Width($bits(i3c_pio_intr_t)), .EdgeTrig('0)) u_pio_intr (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    .event_i      (pio_interrupts),

    .status_en_i  ({reg2hw_i.pio_intr_status_enable.transfer_err_stat_en.q,
                    reg2hw_i.pio_intr_status_enable.transfer_abort_stat_en.q,
                    reg2hw_i.pio_intr_status_enable.resp_ready_stat_en.q,
                    reg2hw_i.pio_intr_status_enable.cmd_queue_ready_stat_en.q,
                    reg2hw_i.pio_intr_status_enable.ibi_status_thld_stat_en.q,
                    reg2hw_i.pio_intr_status_enable.rx_thld_stat_en.q,
                    reg2hw_i.pio_intr_status_enable.tx_thld_stat_en.q}),
    .status_de_o  ({hw2reg_o.pio_intr_status.transfer_err_stat.de,
                    hw2reg_o.pio_intr_status.transfer_abort_stat.de,
                    hw2reg_o.pio_intr_status.resp_ready_stat.de,
                    hw2reg_o.pio_intr_status.cmd_queue_ready_stat.de,
                    hw2reg_o.pio_intr_status.ibi_status_thld_stat.de,
                    hw2reg_o.pio_intr_status.rx_thld_stat.de,
                    hw2reg_o.pio_intr_status.tx_thld_stat.de}),
    .status_d_o   ({hw2reg_o.pio_intr_status.transfer_err_stat.d,
                    hw2reg_o.pio_intr_status.transfer_abort_stat.d,
                    hw2reg_o.pio_intr_status.resp_ready_stat.d,
                    hw2reg_o.pio_intr_status.cmd_queue_ready_stat.d,
                    hw2reg_o.pio_intr_status.ibi_status_thld_stat.d,
                    hw2reg_o.pio_intr_status.rx_thld_stat.d,
                    hw2reg_o.pio_intr_status.tx_thld_stat.d}),
    .force_i      ({reg2hw_i.pio_intr_force.transfer_err_force.qe &
                    reg2hw_i.pio_intr_force.transfer_err_force.q,
                    reg2hw_i.pio_intr_force.transfer_abort_force.qe &
                    reg2hw_i.pio_intr_force.transfer_abort_force.q,
                    reg2hw_i.pio_intr_force.resp_ready_force.qe &
                    reg2hw_i.pio_intr_force.resp_ready_force.q,
                    reg2hw_i.pio_intr_force.cmd_queue_ready_force.qe &
                    reg2hw_i.pio_intr_force.cmd_queue_ready_force.q,
                    reg2hw_i.pio_intr_force.ibi_thld_force.qe &
                    reg2hw_i.pio_intr_force.ibi_thld_force.q,
                    reg2hw_i.pio_intr_force.rx_thld_force.qe &
                    reg2hw_i.pio_intr_force.rx_thld_force.q,
                    reg2hw_i.pio_intr_force.tx_thld_force.q}),
    .status_i     ({reg2hw_i.pio_intr_status.transfer_err_stat.q,
                    reg2hw_i.pio_intr_status.transfer_abort_stat.q,
                    reg2hw_i.pio_intr_status.resp_ready_stat.q,
                    reg2hw_i.pio_intr_status.cmd_queue_ready_stat.q,
                    reg2hw_i.pio_intr_status.ibi_status_thld_stat.q,
                    reg2hw_i.pio_intr_status.rx_thld_stat.q,
                    reg2hw_i.pio_intr_status.tx_thld_stat.q}),
    .signal_en_i  ({reg2hw_i.pio_intr_signal_enable.transfer_err_signal_en.q,
                    reg2hw_i.pio_intr_signal_enable.transfer_abort_signal_en.q,
                    reg2hw_i.pio_intr_signal_enable.resp_ready_signal_en.q,
                    reg2hw_i.pio_intr_signal_enable.cmd_queue_ready_signal_en.q,
                    reg2hw_i.pio_intr_signal_enable.ibi_status_thld_signal_en.q,
                    reg2hw_i.pio_intr_signal_enable.rx_thld_signal_en.q,
                    reg2hw_i.pio_intr_signal_enable.tx_thld_signal_en.q}),

    .intr_o       (intr_pio)
  );

  // Secondary Controller interrupts.
  // TODO: Set interrupt types.
  i3c_intr #(.Width($bits(i3c_stby_cr_intr_t)), .EdgeTrig('0)) u_stby_cr_intr (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    .event_i      (stby_cr_interrupts),

    .status_en_i  ('1),  // No INTR_STATUS_ENABLE for these interrupts.
    .status_de_o  ({hw2reg_o.stby_cr_intr_status.ccc_fatal_rstdaa_err_stat.de,
                    hw2reg_o.stby_cr_intr_status.ccc_unhandled_nack_stat.de,
                    hw2reg_o.stby_cr_intr_status.ccc_param_modified_stat.de,
                    hw2reg_o.stby_cr_intr_status.stby_cr_op_rstact_stat.de,
                    hw2reg_o.stby_cr_intr_status.stby_cr_accept_err_stat.de,
                    hw2reg_o.stby_cr_intr_status.stby_cr_accept_ok_stat.de,
                    hw2reg_o.stby_cr_intr_status.stby_cr_accept_nacked_stat.de,
                    hw2reg_o.stby_cr_intr_status.stby_cr_dyn_addr_stat.de,
                    hw2reg_o.stby_cr_intr_status.crr_response_stat.de,
                    hw2reg_o.stby_cr_intr_status.acr_handoff_err_m3_stat.de,
                    hw2reg_o.stby_cr_intr_status.acr_handoff_err_fail_stat.de,
                    hw2reg_o.stby_cr_intr_status.acr_handoff_ok_primed_stat.de,
                    hw2reg_o.stby_cr_intr_status.acr_handoff_ok_remain_stat.de}),
    .status_d_o   ({hw2reg_o.stby_cr_intr_status.ccc_fatal_rstdaa_err_stat.d,
                    hw2reg_o.stby_cr_intr_status.ccc_unhandled_nack_stat.d,
                    hw2reg_o.stby_cr_intr_status.ccc_param_modified_stat.d,
                    hw2reg_o.stby_cr_intr_status.stby_cr_op_rstact_stat.d,
                    hw2reg_o.stby_cr_intr_status.stby_cr_accept_err_stat.d,
                    hw2reg_o.stby_cr_intr_status.stby_cr_accept_ok_stat.d,
                    hw2reg_o.stby_cr_intr_status.stby_cr_accept_nacked_stat.d,
                    hw2reg_o.stby_cr_intr_status.stby_cr_dyn_addr_stat.d,
                    hw2reg_o.stby_cr_intr_status.crr_response_stat.d,
                    hw2reg_o.stby_cr_intr_status.acr_handoff_err_m3_stat.d,
                    hw2reg_o.stby_cr_intr_status.acr_handoff_err_fail_stat.d,
                    hw2reg_o.stby_cr_intr_status.acr_handoff_ok_primed_stat.d,
                    hw2reg_o.stby_cr_intr_status.acr_handoff_ok_remain_stat.d}),
    .force_i      ({reg2hw_i.stby_cr_intr_force.ccc_fatal_rstdaa_err_force.qe &
                    reg2hw_i.stby_cr_intr_force.ccc_fatal_rstdaa_err_force.q,
                    reg2hw_i.stby_cr_intr_force.ccc_unhandled_nack_force.qe &
                    reg2hw_i.stby_cr_intr_force.ccc_unhandled_nack_force.q,
                    reg2hw_i.stby_cr_intr_force.ccc_param_modified_force.qe &
                    reg2hw_i.stby_cr_intr_force.ccc_param_modified_force.q,
                    reg2hw_i.stby_cr_intr_force.stby_cr_op_rstact_force.qe &
                    reg2hw_i.stby_cr_intr_force.stby_cr_op_rstact_force.q,
                    reg2hw_i.stby_cr_intr_force.stby_cr_accept_err_force.qe &
                    reg2hw_i.stby_cr_intr_force.stby_cr_accept_err_force.q,
                    reg2hw_i.stby_cr_intr_force.stby_cr_accept_ok_force.qe &
                    reg2hw_i.stby_cr_intr_force.stby_cr_accept_ok_force.q,
                    reg2hw_i.stby_cr_intr_force.stby_cr_accept_nacked_force.qe &
                    reg2hw_i.stby_cr_intr_force.stby_cr_accept_nacked_force.q,
                    reg2hw_i.stby_cr_intr_force.stby_cr_dyn_addr_force.qe &
                    reg2hw_i.stby_cr_intr_force.stby_cr_dyn_addr_force.q,
                    reg2hw_i.stby_cr_intr_force.crr_response_force.qe &
                    reg2hw_i.stby_cr_intr_force.crr_response_force.q,
                    4'h0}),  // acr_handoff interrupts do not have force controls.
    .status_i     ({reg2hw_i.stby_cr_intr_status.ccc_fatal_rstdaa_err_stat.q,
                    reg2hw_i.stby_cr_intr_status.ccc_unhandled_nack_stat.q,
                    reg2hw_i.stby_cr_intr_status.ccc_param_modified_stat.q,
                    reg2hw_i.stby_cr_intr_status.stby_cr_op_rstact_stat.q,
                    reg2hw_i.stby_cr_intr_status.stby_cr_accept_err_stat.q,
                    reg2hw_i.stby_cr_intr_status.stby_cr_accept_ok_stat.q,
                    reg2hw_i.stby_cr_intr_status.stby_cr_accept_nacked_stat.q,
                    reg2hw_i.stby_cr_intr_status.stby_cr_dyn_addr_stat.q,
                    reg2hw_i.stby_cr_intr_status.crr_response_stat.q,
                    reg2hw_i.stby_cr_intr_status.acr_handoff_err_m3_stat.q,
                    reg2hw_i.stby_cr_intr_status.acr_handoff_err_fail_stat.q,
                    reg2hw_i.stby_cr_intr_status.acr_handoff_ok_primed_stat.q,
                    reg2hw_i.stby_cr_intr_status.acr_handoff_ok_remain_stat.q}),
    .signal_en_i  ({reg2hw_i.stby_cr_intr_signal_enable.ccc_fatal_rstdaa_err_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.ccc_unhandled_nack_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.ccc_param_modified_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.stby_cr_op_rstact_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.stby_cr_accept_err_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.stby_cr_accept_ok_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.stby_cr_accept_nacked_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.stby_cr_dyn_addr_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.crr_response_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.acr_handoff_err_m3_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.acr_handoff_err_fail_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.acr_handoff_ok_primed_signal_en.q,
                    reg2hw_i.stby_cr_intr_signal_enable.acr_handoff_ok_remain_signal_en.q}),

    .intr_o       (intr_stby_cr)
  );

  // Target-side interrupts; these are additional to those of the Standby Controller.
  // TODO: Set interrupt types.
  i3c_intr #(.Width($bits(i3c_targ_intr_t)), .EdgeTrig('0)) u_targ_intr (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    .event_i      (targ_interrupts),

    .status_en_i  ({reg2hw_i.targ_intr_status_enable.te_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.tx3_desc_ready_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.tx2_desc_ready_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.tx1_desc_ready_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.tx0_desc_ready_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.tx3_thld_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.tx2_thld_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.tx1_thld_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.tx0_thld_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.async_evt_ovl_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.rx_buffer_ovl_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.transfer_err_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.transfer_abort_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.async_evt_ready_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.rx_desc_ready_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.ibi_status_thld_stat_en.q,
                    reg2hw_i.targ_intr_status_enable.rx_thld_stat_en.q}),
    .status_de_o  ({hw2reg_o.targ_intr_status.te_stat.de,
                    hw2reg_o.targ_intr_status.tx3_desc_ready_stat.de,
                    hw2reg_o.targ_intr_status.tx2_desc_ready_stat.de,
                    hw2reg_o.targ_intr_status.tx1_desc_ready_stat.de,
                    hw2reg_o.targ_intr_status.tx0_desc_ready_stat.de,
                    hw2reg_o.targ_intr_status.tx3_thld_stat.de,
                    hw2reg_o.targ_intr_status.tx2_thld_stat.de,
                    hw2reg_o.targ_intr_status.tx1_thld_stat.de,
                    hw2reg_o.targ_intr_status.tx0_thld_stat.de,
                    hw2reg_o.targ_intr_status.async_evt_ovl_stat.de,
                    hw2reg_o.targ_intr_status.rx_buffer_ovl_stat.de,
                    hw2reg_o.targ_intr_status.transfer_err_stat.de,
                    hw2reg_o.targ_intr_status.transfer_abort_stat.de,
                    hw2reg_o.targ_intr_status.async_evt_ready_stat.de,
                    hw2reg_o.targ_intr_status.rx_desc_ready_stat.de,
                    hw2reg_o.targ_intr_status.ibi_status_thld_stat.de,
                    hw2reg_o.targ_intr_status.rx_thld_stat.de}),
    .status_d_o   ({hw2reg_o.targ_intr_status.te_stat.d,
                    hw2reg_o.targ_intr_status.tx3_desc_ready_stat.d,
                    hw2reg_o.targ_intr_status.tx2_desc_ready_stat.d,
                    hw2reg_o.targ_intr_status.tx1_desc_ready_stat.d,
                    hw2reg_o.targ_intr_status.tx0_desc_ready_stat.d,
                    hw2reg_o.targ_intr_status.tx3_thld_stat.d,
                    hw2reg_o.targ_intr_status.tx2_thld_stat.d,
                    hw2reg_o.targ_intr_status.tx1_thld_stat.d,
                    hw2reg_o.targ_intr_status.tx0_thld_stat.d,
                    hw2reg_o.targ_intr_status.async_evt_ovl_stat.d,
                    hw2reg_o.targ_intr_status.rx_buffer_ovl_stat.d,
                    hw2reg_o.targ_intr_status.transfer_err_stat.d,
                    hw2reg_o.targ_intr_status.transfer_abort_stat.d,
                    hw2reg_o.targ_intr_status.async_evt_ready_stat.d,
                    hw2reg_o.targ_intr_status.rx_desc_ready_stat.d,
                    hw2reg_o.targ_intr_status.ibi_status_thld_stat.d,
                    hw2reg_o.targ_intr_status.rx_thld_stat.d}),
    .force_i      ({reg2hw_i.targ_intr_force.te_force.qe &
                    reg2hw_i.targ_intr_force.te_force.q,
                    reg2hw_i.targ_intr_force.tx3_desc_ready_force.qe &
                    reg2hw_i.targ_intr_force.tx3_desc_ready_force.q,
                    reg2hw_i.targ_intr_force.tx2_desc_ready_force.qe &
                    reg2hw_i.targ_intr_force.tx2_desc_ready_force.q,
                    reg2hw_i.targ_intr_force.tx1_desc_ready_force.qe &
                    reg2hw_i.targ_intr_force.tx1_desc_ready_force.q,
                    reg2hw_i.targ_intr_force.tx0_desc_ready_force.qe &
                    reg2hw_i.targ_intr_force.tx0_desc_ready_force.q,
                    reg2hw_i.targ_intr_force.tx3_thld_force.qe &
                    reg2hw_i.targ_intr_force.tx3_thld_force.q,
                    reg2hw_i.targ_intr_force.tx2_thld_force.qe &
                    reg2hw_i.targ_intr_force.tx2_thld_force.q,
                    reg2hw_i.targ_intr_force.tx1_thld_force.qe &
                    reg2hw_i.targ_intr_force.tx1_thld_force.q,
                    reg2hw_i.targ_intr_force.tx0_thld_force.qe &
                    reg2hw_i.targ_intr_force.tx0_thld_force.q,
                    reg2hw_i.targ_intr_force.async_evt_ovl_force.qe &
                    reg2hw_i.targ_intr_force.async_evt_ovl_force.q,
                    reg2hw_i.targ_intr_force.rx_buffer_ovl_force.qe &
                    reg2hw_i.targ_intr_force.rx_buffer_ovl_force.q,
                    reg2hw_i.targ_intr_force.transfer_err_force.qe &
                    reg2hw_i.targ_intr_force.transfer_err_force.q,
                    reg2hw_i.targ_intr_force.transfer_abort_force.qe &
                    reg2hw_i.targ_intr_force.transfer_abort_force.q,
                    reg2hw_i.targ_intr_force.async_evt_ready_force.qe &
                    reg2hw_i.targ_intr_force.async_evt_ready_force.q,
                    reg2hw_i.targ_intr_force.rx_desc_ready_force.qe &
                    reg2hw_i.targ_intr_force.rx_desc_ready_force.q,
                    reg2hw_i.targ_intr_force.ibi_thld_force.qe &
                    reg2hw_i.targ_intr_force.ibi_thld_force.q,
                    reg2hw_i.targ_intr_force.rx_thld_force.qe &
                    reg2hw_i.targ_intr_force.rx_thld_force.q}),
    .status_i     ({reg2hw_i.targ_intr_status.te_stat.q,
                    reg2hw_i.targ_intr_status.tx3_desc_ready_stat.q,
                    reg2hw_i.targ_intr_status.tx2_desc_ready_stat.q,
                    reg2hw_i.targ_intr_status.tx1_desc_ready_stat.q,
                    reg2hw_i.targ_intr_status.tx0_desc_ready_stat.q,
                    reg2hw_i.targ_intr_status.tx3_thld_stat.q,
                    reg2hw_i.targ_intr_status.tx2_thld_stat.q,
                    reg2hw_i.targ_intr_status.tx1_thld_stat.q,
                    reg2hw_i.targ_intr_status.tx0_thld_stat.q,
                    reg2hw_i.targ_intr_status.async_evt_ovl_stat.q,
                    reg2hw_i.targ_intr_status.rx_buffer_ovl_stat.q,
                    reg2hw_i.targ_intr_status.transfer_err_stat.q,
                    reg2hw_i.targ_intr_status.transfer_abort_stat.q,
                    reg2hw_i.targ_intr_status.async_evt_ready_stat.q,
                    reg2hw_i.targ_intr_status.rx_desc_ready_stat.q,
                    reg2hw_i.targ_intr_status.ibi_status_thld_stat.q,
                    reg2hw_i.targ_intr_status.rx_thld_stat.q}),
    .signal_en_i  ({reg2hw_i.targ_intr_signal_enable.te_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.tx3_desc_ready_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.tx2_desc_ready_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.tx1_desc_ready_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.tx0_desc_ready_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.tx3_thld_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.tx2_thld_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.tx1_thld_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.tx0_thld_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.async_evt_ovl_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.rx_buffer_ovl_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.transfer_err_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.transfer_abort_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.async_evt_ready_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.rx_desc_ready_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.ibi_status_thld_signal_en.q,
                    reg2hw_i.targ_intr_signal_enable.rx_thld_signal_en.q}),

    .intr_o       (intr_targ)
  );

  // A number of the Standby Controller-related registers are implemented within a submodule because
  // they impose involved conditions about when writing is permissible.
  i3c_stby_cr_regs u_stby_cr_regs (
    .clk_i                    (clk_i),
    .rst_ni                   (rst_ni),

    // Software register access.
    .reg2hw_i                 (reg2hw_i),
    // Currently the Active Controller?
    .ac_current_own_i         (ac_current_own),
    // Software writes to the `CONTROLLER_DEVICE_ADDR` register.
    .ctrladdr_qe_i            (reg2hw_i.controller_device_addr.dynamic_addr_valid.qe &
                               reg2hw_i.controller_device_addr.dynamic_addr.qe),
    .ctrladdr_q_i             ({reg2hw_i.controller_device_addr.dynamic_addr_valid.q,
                                reg2hw_i.controller_device_addr.dynamic_addr.q}),
    // Setting the Standby Controller Dynamic Address.
    .stby_cr_dynaddr_de_i     (stby_cr_dynaddr_de),
    .stby_cr_dynaddr_d_i      (stby_cr_dynaddr_d),
    // Setting the RSTACT.
    .rstact_de_i              (targ_rstact_de),
    .rstact_d_i               (targ_rstact_d),

    // Register state.
    .stby_cr_control_o        (hw2reg_o.stby_cr_control),
    .stby_cr_device_addr_o    (hw2reg_o.stby_cr_device_addr),
    .stby_cr_device_char_o    (hw2reg_o.stby_cr_device_char),
    .stby_cr_device_pid_lo_o  (hw2reg_o.stby_cr_device_pid_lo),
    .stby_cr_config_getcaps_o (hw2reg_o.stby_cr_ccc_config_getcaps),
    .stby_cr_config_rstact_o  (hw2reg_o.stby_cr_ccc_config_rstact_params)
  );

  // HCI information fields.
  // - `BASE` is at offset 'h100 within the I3C block register space.
  // - offsets are specified relative to that base.
  localparam bit [11:0] BASE_OFFSET = 12'h100;
  assign hw2reg_o.hci_version.d = 'h120;
  // Controller Device Address.
  // - as the Active Controller this may be set by software before Controller Role handoff.
  // - when in Standby Controller Mode this reflects the assigned dynamic address.
  assign hw2reg_o.controller_device_addr.dynamic_addr_valid.d =
         hw2reg_o.stby_cr_device_addr.dynamic_addr_valid.d;
  assign hw2reg_o.controller_device_addr.dynamic_addr.d =
         hw2reg_o.stby_cr_device_addr.dynamic_addr.d;
  // Host Controller Capabilities.
  assign hw2reg_o.hc_capabilities.sg_capability_dc_en.d  = 1'b0;
  assign hw2reg_o.hc_capabilities.sg_capability_ibi_en.d = 1'b0;
  assign hw2reg_o.hc_capabilities.sg_capability_cr_en.d  = 1'b0;
  assign hw2reg_o.hc_capabilities.cmd_size.d             = 2'b00;
  assign hw2reg_o.hc_capabilities.schedule_commands_en.d = 1'b0;
  assign hw2reg_o.hc_capabilities.ibi_credit_count_en.d  = 1'b0;
  assign hw2reg_o.hc_capabilities.ibi_data_abort_en.d    = 1'b0;  // Not implemented.
  assign hw2reg_o.hc_capabilities.cmd_ccc_defbyte.d      = 1'b1;
  assign hw2reg_o.hc_capabilities.hdr_ts_en.d            = 1'b0;  // HDR-Ternary not in I3C Basic.
  assign hw2reg_o.hc_capabilities.hdr_ddr_en.d           = 1'b1;
  assign hw2reg_o.hc_capabilities.standby_cr_cap.d       = 1'b1;
  assign hw2reg_o.hc_capabilities.auto_command.d         = 1'b1;
  assign hw2reg_o.hc_capabilities.combo_command.d        = 1'b0;  // Not supported presently.
  // Active Controller indication.
  assign hw2reg_o.present_state.d = ac_current_own;
  // Addressing offsets.
  assign hw2reg_o.pio_section_offset.d              = 16'(I3C_HCI_PORTS_OFFSET) -
                                                      16'(BASE_OFFSET);
  assign hw2reg_o.dat_section_offset.entry_size.d   = 'h0;
  assign hw2reg_o.dat_section_offset.table_size.d   = 7'(NumDATEntries);
  assign hw2reg_o.dat_section_offset.table_offset.d = I3C_DAT_OFFSET - BASE_OFFSET;
  assign hw2reg_o.dct_section_offset.entry_size.d   = 'h0;
  assign hw2reg_o.dct_section_offset.table_index.d  = dct_idx;
  assign hw2reg_o.dct_section_offset.table_size.d   = 7'(NumDCTEntries);
  assign hw2reg_o.dct_section_offset.table_offset.d = I3C_DCT_OFFSET - BASE_OFFSET;
  assign hw2reg_o.ring_headers_section_offset.d     = '0;
  // The start of the Extended Capabilities linked-list; we know that Hardware Identification is
  // the first entry in the list.
  assign hw2reg_o.ext_caps_section_offset.d         = I3C_ID_EXTCAP_HEADER_OFFSET;
  // Internal Control Command Subtype Support.
  assign hw2reg_o.int_ctrl_cmds_en.icc_support.d         = 1'b1;
  assign hw2reg_o.int_ctrl_cmds_en.mipi_cmds_supported.d = 'h107a;
  // Device Context Base Address (applicable only to DMA).
  assign hw2reg_o.dev_ctx_base_lo.d      = '0;
  assign hw2reg_o.dev_ctx_base_hi.d      = '0;
  assign hw2reg_o.dev_ctx_sg.blp.d       = 1'b0;
  assign hw2reg_o.dev_ctx_sg.list_size.d = '0;
  // Report the dimensions of queues and data buffers.
  assign hw2reg_o.queue_size.tx_data_buffer_size.d   = 8'(reg2hw_i.ctrl_txbuf_config.size_val.q);
  assign hw2reg_o.queue_size.rx_data_buffer_size.d   = 8'(reg2hw_i.ctrl_rxbuf_config.size_val.q);
  assign hw2reg_o.queue_size.ibi_status_size.d       = 8'(reg2hw_i.ibi_config.size_val.q);
  assign hw2reg_o.queue_size.cr_queue_size.d         = 8'(reg2hw_i.command_queue_config.size_val.q);
  assign hw2reg_o.alt_queue_size.ext_ibi_queue_en.d  = 1'b0;
  assign hw2reg_o.alt_queue_size.alt_resp_queue_en.d = 1'b1;
  assign hw2reg_o.alt_queue_size.alt_resp_queue_size.d =
         8'(reg2hw_i.response_queue_config.size_val.q);

  // ----- The IP implements a number of Extended Capabilities (see HCI Table 82). -----

  // Hardware Identification (Extended Capability).
  assign hw2reg_o.id_extcap_header.cap_length.d = I3C_ID_EXTCAP_HEADER_CAP_LENGTH_RESVAL;
  assign hw2reg_o.id_extcap_header.cap_id.d = I3C_ID_EXTCAP_HEADER_CAP_ID_RESVAL;
  assign hw2reg_o.comp_manufacturer.d = CompManufacturer;
  assign hw2reg_o.comp_version.d      = CompVersion;
  assign hw2reg_o.comp_type.d         = CompType;

  // Controller Extended Configuration (Extended Capability).
  assign hw2reg_o.ctrl_cfg_extcap_header.cap_length.d =
            I3C_CTRL_CFG_EXTCAP_HEADER_CAP_LENGTH_RESVAL;
  assign hw2reg_o.ctrl_cfg_extcap_header.cap_id.d = I3C_CTRL_CFG_EXTCAP_HEADER_CAP_ID_RESVAL;
  // TODO: This value will likely need to be configuration/parameter-dependent.
  assign hw2reg_o.controller_config.d = 2'b11;

  // Dead Bus Recovery (Extended Capability).
  assign hw2reg_o.dbr_extcap_header.cap_length.d = I3C_DBR_EXTCAP_HEADER_CAP_LENGTH_RESVAL;
  assign hw2reg_o.dbr_extcap_header.cap_id.d     = I3C_DBR_EXTCAP_HEADER_CAP_ID_RESVAL;

  // Debug Specific (Extended Capability).
  assign hw2reg_o.debug_extcap_header.cap_length.d = I3C_DEBUG_EXTCAP_HEADER_CAP_LENGTH_RESVAL;
  assign hw2reg_o.debug_extcap_header.cap_id.d     = I3C_DEBUG_EXTCAP_HEADER_CAP_ID_RESVAL;
  assign hw2reg_o.sched_cmds_debug.err_occurred.d  = 1'b0;

  // TODO: These values are restricted to 8 bits by the HCI; we have 10 bit used/avail values.
  assign hw2reg_o.queue_status_level.ibi_status_cnt.d        = fifo_state[FIFO_IBIStD].used;
  assign hw2reg_o.queue_status_level.ibi_buffer_lvl.d        = fifo_state[FIFO_IBIQ].used;
  // These two fields are specified as _entries_ and not DWORDs; Commands are _two_ DWORDs.
  assign hw2reg_o.queue_status_level.response_buffer_lvl.d   = fifo_state[FIFO_RspQ].used;
  assign hw2reg_o.queue_status_level.cmd_queue_free_lvl.d    = fifo_state[FIFO_CmdQ].avail >> 1;
  assign hw2reg_o.data_buffer_status_level.rx_buf_lvl.d      = fifo_state[FIFO_RxBuf].used;
  assign hw2reg_o.data_buffer_status_level.tx_buf_free_lvl.d = fifo_state[FIFO_TxBuf].avail;

  // Target-side queue levels.
  assign hw2reg_o.targ_queue_status_level.rx_buf_lvl.d    = fifo_state[FIFO_RxTarg].used;
  assign hw2reg_o.targ_queue_status_level.rx_desc_lvl.d   = fifo_state[FIFO_RxDTarg].used;
  assign hw2reg_o.targ_queue_status_level.async_evt_lvl.d = fifo_state[FIFO_AsyncTarg].used;
  assign hw2reg_o.targ_queue_status_level.ibi_free_lvl.d  = fifo_state[FIFO_IBITarg].avail;
  // Individual Virtual Target Tx queue levels.
  for (genvar t = 0; t < NumTargets; t++) begin
    assign hw2reg_o.targ_tx_queue_status_level[t].tx_desc_free_lvl.d =
           fifo_state[FIFO_TxDTarg0 + t].used;
    assign hw2reg_o.targ_tx_queue_status_level[t].tx_buf_free_lvl.d =
           fifo_state[FIFO_TxTarg0 + t].used;
  end
  // Check that the FIFO numbers are indeed contiguous.
  if (FIFO_TxTarg1  != FIFO_TxTarg0  + 1) $fatal(1, "Tx FIFO identifiers are not contiguous");
  if (FIFO_TxDTarg1 != FIFO_TxDTarg0 + 1) $fatal(1, "Tx Desc FIFO identifiers are not contiguous");
  // Complete the unused fields too.
  for (genvar t = NumTargets; t < MaxTargets; t++) begin
    assign hw2reg_o.targ_tx_queue_status_level[t].tx_desc_free_lvl.d = 'b0;
    assign hw2reg_o.targ_tx_queue_status_level[t].tx_buf_free_lvl.d  = 'b0;
  end

  // Scheduled Commands are not supported.
  assign hw2reg_o.sched_cmds_debug.tick_interval.d = '0;
  assign hw2reg_o.sched_cmds_debug.entity_id.d     = '0;
  assign hw2reg_o.sched_cmds_debug.err_type.d      = '0;
  assign hw2reg_o.sched_cmds_debug.inst_id.d       = '0;
  assign hw2reg_o.sched_cmds_debug.sched_handler.d = '0;

  // Standby Controller Mode (Extended Capability).
  assign hw2reg_o.stby_cr_extcap_header.cap_length.d = I3C_STBY_CR_EXTCAP_HEADER_CAP_LENGTH_RESVAL;
  assign hw2reg_o.stby_cr_extcap_header.cap_id.d     = I3C_STBY_CR_EXTCAP_HEADER_CAP_ID_RESVAL;

  // We support all address assignment methods as well as offering a TTI.
  assign hw2reg_o.stby_cr_capabilities.daa_entdaa_support.d  = 1'b1;
  assign hw2reg_o.stby_cr_capabilities.daa_setdasa_support.d = 1'b1;
  assign hw2reg_o.stby_cr_capabilities.daa_setaasa_support.d = 1'b1;
  assign hw2reg_o.stby_cr_capabilities.target_xact_support.d = 1'b1;  // Includes a TTI.
  assign hw2reg_o.stby_cr_capabilities.simple_crr_support.d  = 1'b1;  // Standby Controller support.

  // Vendor Specific (Extended Capability).
  // - Target Transaction Interface.
  assign hw2reg_o.tti_extcap_header.cap_length.d = I3C_TTI_EXTCAP_HEADER_CAP_LENGTH_RESVAL;
  assign hw2reg_o.tti_extcap_header.cap_id.d     = I3C_TTI_EXTCAP_HEADER_CAP_ID_RESVAL;

  // Maximum transfer lengths for each Target.
  always_comb begin
    for (int unsigned t = 0; t < MaxTargets; t++) begin
      if (t < NumTargets) begin
        hw2reg_o.targ_rw_len[t].mwl.de = targ_mwl_de[t];
        hw2reg_o.targ_rw_len[t].mrl.de = targ_mrl_de[t];
        hw2reg_o.targ_ibi_len[t].de    = targ_ibi_de[t];
        hw2reg_o.targ_rw_len[t].mwl.d  = targ_mwl_d;
        hw2reg_o.targ_rw_len[t].mrl.d  = targ_mrl_d;
        hw2reg_o.targ_ibi_len[t].d     = targ_ibi_d;
      end else begin
        hw2reg_o.targ_rw_len[t].mwl.de = 1'b0;
        hw2reg_o.targ_rw_len[t].mrl.de = 1'b0;
        hw2reg_o.targ_ibi_len[t].de    = 1'b0;
        hw2reg_o.targ_rw_len[t].mwl.d  = 16'b0;
        hw2reg_o.targ_rw_len[t].mrl.d  = 16'b0;
        hw2reg_o.targ_ibi_len[t].d     = 8'b0;
      end
    end
  end
  // Present Group Addressing state in the TTI registers.
  for (genvar grp = 0; grp < MaxGroups; grp++) begin
    assign hw2reg_o.targ_group[grp].group_addr.de = targ_grp_addr_de[grp];
    assign hw2reg_o.targ_group[grp].group_addr.d  = targ_grp_addr_d[grp];
    assign hw2reg_o.targ_group[grp].targets.de    = targ_grp_targ_de[grp];
    assign hw2reg_o.targ_group[grp].targets.d     = targ_grp_targ_d[grp];
  end

  assign hw2reg_o.reset_det_status.active.de     = 1'b1;
  assign hw2reg_o.reset_det_status.active.d      = rstdet_rsp_i.active;
  assign hw2reg_o.reset_det_status.wake_up.de    = 1'b1;
  assign hw2reg_o.reset_det_status.wake_up.d     = rstdet_rsp_i.wake_up_det;
  assign hw2reg_o.reset_det_status.rst_periph.de = 1'b1;
  assign hw2reg_o.reset_det_status.rst_periph.d  = rstdet_rsp_i.peri_rst_det;
  assign hw2reg_o.reset_det_status.rst_target.de = 1'b1;
  assign hw2reg_o.reset_det_status.rst_target.d  = rstdet_rsp_i.targ_rst_det;

  // Termination of Extended Capability linked-list.
  assign hw2reg_o.term_extcap_header.cap_length.d = 16'h1;
  assign hw2reg_o.term_extcap_header.cap_id.d     = 'h0;

endmodule
