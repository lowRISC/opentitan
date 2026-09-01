// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I3C Target core.

`include "prim_assert.sv"

module i3c_target
  import i3c_consts_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
  import i3c_target_pkg::*;
  import i3c_targ_ext_pkg::*;
#(
  // Number of target(s) or target group(s) presented simultaneously on the I3C bus, including the
  // Standby Controller Role.
  parameter int unsigned NumTargets = 2,
  parameter int unsigned DataWidth  = 32,
  parameter int unsigned FIFODepthW = i3c_fifo_pkg::DepthW,
  parameter bit          TargetExt  = 1'b0
) (
  // Clock and reset for system interface.
  input                     clk_i,
  input                     rst_ni,

  // I3C clock signal from the Active Controller, inverted.
  input                     scl_ni,
  // Reset for transceiver logic.
  input                     trx_rst_ni,

  // Control inputs.
  input                     enable_i,
  input                     stby_cr_enabled_i,
  input                     sw_reset_i,
  input                     async_evt_rst_i,
  // TODO: These two signals are currently unused
  input                     hdr_exit_det_i,
  input                     hdr_restart_det_i,

  // Configuration settings.
  input  i3c_reg2hw_t       reg2hw_i,

  // Standby Controller configuration settings.
  input               [1:0] stby_cr_enable_init_i,
  input                     stby_cr_cr_req_send_i,
  input               [7:0] stby_cr_staddr_i,
  input               [7:0] stby_cr_dynaddr_i,
  input               [7:0] stby_cr_dcr_i,
  input               [7:0] stby_cr_bcr_i,
  input              [47:0] stby_cr_pid_i,
  input  i3c_rstact_e       rstact_i,
  // Blocked device addresses.
  input               [6:0] addr_blocked_i[NumBlocked],
  input               [6:0] mask_blocked_i[NumBlocked],

  // Control outputs.
  output                    hdr_exit_det_en_o,

  // Bus signals, already synchronized to the IP clock domain.
  input                     scl_i,
  input                     sda_i,
  // Bus status signals.
  input                     bus_avail_i,
  input                     bus_idle_i,

  // State information, presented via TTI.
  output   [NumTargets-1:0] dynaddr_de_o,
  output                    dynaddr_valid_d_o,
  output              [6:0] dynaddr_d_o[NumTargets],
  output                    virt_targ_det_o,
  output   [NumTargets-1:0] mwl_de_o,
  output   [NumTargets-1:0] mrl_de_o,
  output   [NumTargets-1:0] ibi_de_o,
  output             [15:0] mwl_d_o,
  output             [15:0] mrl_d_o,
  output              [7:0] ibi_d_o,
  output i3c_endis_event_t  endis_event_o,
  // Update RSTACT in response to CCC.
  output                    rstact_de_o,
  output i3c_rstact_e       rstact_d_o,
  output                    grp_addr_de_o[MaxGroups],
  output                    grp_targ_de_o[MaxGroups],
  output              [6:0] grp_addr_d_o[MaxGroups],
  output   [NumTargets-1:0] grp_targ_d_o[MaxGroups],
  output   [NumTargets-1:0] act_state_de_o,
  output              [1:0] act_state_d_o,
  output   [NumTargets-1:0] endxfer_cand_de_o,
  output              [2:0] endxfer_cand_d_o,
  output   [NumTargets-1:0] endxfer_de_o,
  output              [2:0] endxfer_d_o[NumTargets],
  output                    vend_test_mode_o,
  output                    protocol_error_o,
  output                    hj_request_clear_o,

  // Interrupts to the TTI.
  output i3c_targ_intr_t    intr_o,

  // Target device descriptions to the transceiver.
  output i3c_targ_dev_t     targ_dev_o[NumTargets],
  // Group address descriptions to the transceiver.
  output i3c_grp_addr_t     grp_addr_o[NumGroups],

  // Start request to the transceiver.
  // - SDA lowered to request Start signaling, and partial address phase.
  output                    sreq_sda_od_en_o,
  output                    sreq_sda_o,
  // TODO: Handoff of the address arbitration to the transceiver logic.

  // Status indications from the transceiver. Originates in SCL domain, must be glitch free.
  input                     rep_start_det_i,
  input                     stop_det_i,
  input                     ddr_mode_i,

  // Transmission from Virtual Target(s) suspended.
  output   [NumTargets-1:0] suspend_tx_o,
  // IBI Transmission suspended.
  output                    ibi_suspend_tx_o,
  // Clear the Abort status when transmission is resumed.
  output   [NumTargets-1:0] abort_clr_o,
  output                    ibi_abort_clr_o,

  // Transmission Descriptor access.
  output                    tx_desc_rready_o[NumTargets],
  input                     tx_desc_rvalid_i[NumTargets],
  input     [DataWidth-1:0] tx_desc_rdata_i[NumTargets],
  input      [FIFODepthW:0] tx_desc_rused_i[NumTargets],
  input      [FIFODepthW:0] tx_desc_ravail_i[NumTargets],

  // Reception Descriptor access.
  output                    rx_desc_wvalid_o,
  output    [DataWidth-1:0] rx_desc_wdata_o,
  input                     rx_desc_wready_i,
  input      [FIFODepthW:0] rx_desc_wused_i,
  input                     rx_desc_wfull_i,

  // In-Band Interrupt Descriptor access.
  output                    ibi_desc_rready_o,
  input                     ibi_desc_rvalid_i,
  input     [DataWidth-1:0] ibi_desc_rdata_i,
  input      [FIFODepthW:0] ibi_desc_ravail_i,

  // Buffer reading.
  output                    buf_rready_o[NumTargets],
  input                     buf_rvalid_i[NumTargets],
  input     [DataWidth-1:0] buf_rdata_i[NumTargets],
  input                     buf_rempty_i[NumTargets],
  input      [FIFODepthW:0] buf_rused_i[NumTargets],
  input      [FIFODepthW:0] buf_ravail_i[NumTargets],

  // In-Band Interrupt reading.
  output                    ibi_rready_o,
  input                     ibi_rvalid_i,
  input     [DataWidth-1:0] ibi_rdata_i,
  input                     ibi_rempty_i,
  input      [FIFODepthW:0] ibi_rused_i,

  // Transmit data to the transceiver, for Private Read transfers.
  output logic              trx_dvalid_o[NumTargets],
  input                     trx_dready_i[NumTargets],
  output i3c_targ_trx_txd_t trx_dreq_o[NumTargets],

  // Transmit data for Direct Read CCCs.
  output logic              trx_ctvalid_o,
  input                     trx_ctready_i,
  output i3c_targ_trx_txc_t trx_ctreq_o,

  // Arbitration requests to the transceiver.
  output logic              trx_avalid_o,
  input                     trx_aready_i,
  output i3c_targ_trx_arb_t trx_areq_o,

  // Received data from the transceiver logic; Private Writes and Write CCCs.
  input                     trx_rtoggle_i,
  input  i3c_targ_trx_rxd_t trx_rxd_i,

  // Buffer writing.
  output                    buf_wvalid_o,
  output    [DataWidth-1:0] buf_wdata_o,
  input                     buf_wready_i,
  input      [FIFODepthW:0] buf_wused_i,  // TODO: Unused, possibly not needed
  input      [FIFODepthW:0] buf_wavail_i,

  // Asynchronous Event Queue.
  output                    async_wvalid_o,
  output    [DataWidth-1:0] async_wdata_o,
  input                     async_wready_i,
  input                     async_empty_i,

  // Target Reset Detector request/response.
  output i3c_rstdet_req_t   rstdet_req_o,
  input  i3c_rstdet_rsp_t   rstdet_rsp_i,

  // Setting the Standby Controller Dynamic Address.
  output                    stby_cr_dynaddr_de_o,
  output              [7:0] stby_cr_dynaddr_d_o,  // Validity indicator in MSB.

  // Broadcast CCCs received in Standby Controller mode.
  output                    stby_bcst_wvalid_o,
  output    [DataWidth-1:0] stby_bcst_wdata_o,
  input                     stby_bcst_wready_i,

  // Target Errors (TE[6:0], Table 43).
  input               [6:0] trx_te_i,
  output              [6:0] targ_error_o,

  // Data sink status signals.
  output       [BufAddrW:0] sink_dwords_left_o,
  output                    sink_active_o,
  output                    sink_error_o,

  // Extension hardware.
  output                    ext_present_o,
  output             [14:0] ext_info_o,
  input  i3c_reg2targ_ext_t ext_reg2hw_i,
  output i3c_targ_ext2reg_t ext_hw2reg_o,

  // Diagnostic visibility into Target core state.
  output              [7:0] fsm_state_o
);

  import i3c_tti_pkg::*;

  // I3C address of Standby Controller when enabled.
  // Note: the `d` fields are that persistent state (rather than `q`) because this register is
  // declared as `hwext` and implemented in `i3c_stby_cr_regs`.
  logic stby_cr_staddr_valid, stby_cr_dynaddr_valid;
  assign stby_cr_staddr_valid = stby_cr_staddr_i[7];  // MSB indicates the validity of the address.
  assign stby_cr_dynaddr_valid = stby_cr_dynaddr_i[7];
  logic [6:0] stby_cr_addr;
  // Use a valid static address only until a valid dynamic address has been supplied.
  assign stby_cr_addr = stby_cr_dynaddr_valid ? stby_cr_dynaddr_i[6:0] :
                                                {7{stby_cr_staddr_valid}} & stby_cr_staddr_i[6:0];

  // Device description for each Target in turn.
  i3c_targ_dev_t targ_dev[NumTargets];
  always_comb begin
    // Ensure that all target descriptions have been initialized.
    // - use a valid static address only until a valid dynamic address has been supplied.
    for (int unsigned t = 0; t < NumTargets; t++) begin
      logic dynaddr_valid, stataddr_valid;

      stataddr_valid = reg2hw_i.targ_addr[t].static_addr_valid.q;
      dynaddr_valid  = reg2hw_i.targ_addr[t].dynamic_addr_valid.q;

      targ_dev[t] = '0;
      targ_dev[t].en            = reg2hw_i.targ_enable[t].q;
      targ_dev[t].addr          = dynaddr_valid ? reg2hw_i.targ_addr[t].dynamic_addr.q
                                                : reg2hw_i.targ_addr[t].static_addr.q;
      targ_dev[t].addr_valid    = dynaddr_valid | stataddr_valid;
      targ_dev[t].addr_dynamic  = dynaddr_valid;

      targ_dev[t].en_write_nack = reg2hw_i.targ_info[t].endxfer_wr_nack.q;
      targ_dev[t].en_write_term = reg2hw_i.targ_info[t].endxfer_wr_early_term.q;
      targ_dev[t].en_early_crc  = reg2hw_i.targ_info[t].endxfer_crc_early.q;
    end
    // The Standby Controller, when enabled, replacing the first Target.
    if (stby_cr_enabled_i) begin
      targ_dev[0].en            = reg2hw_i.targ_control.stby_cr_support.q;
      targ_dev[0].addr          = stby_cr_addr;
      targ_dev[0].addr_valid    = stby_cr_dynaddr_valid | stby_cr_staddr_valid;
      targ_dev[0].addr_dynamic  = stby_cr_dynaddr_valid;
    end
  end
  assign targ_dev_o = targ_dev;

  // Group membership description for each group in turn.
  for (genvar g = 0; g < NumGroups; g++) begin : g_assign_grp_addr
    assign grp_addr_o[g] = '{
      addr:       reg2hw_i.targ_group[g].group_addr.q,
      addr_valid: |reg2hw_i.targ_group[g].targets.q[NumTargets-1:0],
      targets:    reg2hw_i.targ_group[g].targets.q[NumTargets-1:0]
    };
  end

  // This module handles the CDC transitions between the Core FSM which operates on the main IP
  // clock, and the Transceiver logic which operates on the Controller-supplied I3C clock (SCL).
  //
  // It is important to note that the SCL clock does not run continuously, operates with variable
  // timing and frequency, and will be gated off at times that the transceiver logic must not be
  // sensitive to activity on the I3C bus. A maximum sustained frequency of 12.5MHz may be assumed.
  // For short bursts, up to 12.9MHz may occur (Table 50).

  // Some independent level-sensitive signals may be synchronized in the conventional fashion.
  // - response from the Target Reset Detector; multiple, but independent bits.
  // TODO: `rstdet_rsp_sync` is currently unused (unread)
  i3c_rstdet_rsp_t rstdet_rsp_sync;
  // - HDR-DDR mode indication, on/off.
  logic ddr_mode_sync;
  prim_flop_2sync #(
    .Width(1 + $bits(i3c_rstdet_rsp_t))
  ) u_in_sync (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .d_i   ({ddr_mode_i,    rstdet_rsp_i}),
    .q_o   ({ddr_mode_sync, rstdet_rsp_sync})
  );

  // Synchronize status signals from the transceiver logic and produce single-cycle pulses on the
  // rising edge (`stop_det_i` in particular remains asserted for a long time because the I3C bus is
  // becoming idle at that point).
  // - repeated start (Sr) detected.
  logic rep_start_det;
  // - stop (P) detected.
  logic stop_det;
  // - propagation of Target Error signals into the IP core; these are expected to be asserted for
  //   just a single cycle in the SCL clock domain but the IP clock is sufficiently faster (at least
  //   50MHz / 12.9MHz = 3.88 times) which means that the pulse will not be missed. We also need an
  //   edge detector in the system clock domain to ensure every TE pulse from the SCL domain
  //   registers as a single tick in the connected error counters.
  prim_edge_detector #(
    .Width     ($bits(trx_te_i) + 2),
    .ResetValue('0),
    .EnSync    (1'b1)
  ) u_edge_det (
    .clk_i,
    .rst_ni,
    .d_i              ({trx_te_i,     stop_det_i, rep_start_det_i}),
    .q_sync_o         (),  // Not used
    .q_posedge_pulse_o({targ_error_o, stop_det,   rep_start_det}),
    .q_negedge_pulse_o()  // Not used
  );

  // Target Reset Detector request.
  // TODO: Needs to interact with the RSTACT CCC handling when that exists.
  assign rstdet_req_o = '{
    activate:   enable_i, // TODO: This is incomplete.
    deep_sleep: reg2hw_i.reset_det_ctrl.sleep_req.q,
    rst_periph: reg2hw_i.reset_det_ctrl.rst_periph_en.q && (rstact_i == RstAct_ResetPeripheral),
    rst_target: reg2hw_i.reset_det_ctrl.rst_target_en.q && (rstact_i == RstAct_ResetTarget)
  };

  // Present read data and status information to the transceiver logic for each Target in turn.
  // - this must be done preemptively because Private Read data must be returned by the transceiver
  //   logic almost immediately following a successful match against the device address.
  // - subsequent reads can rely upon the transmission time giving enough time to respond.
  //
  // Private Read transfers.
  logic txd_toggle_out[NumTargets];
  logic txd_toggle_in[NumTargets];
  i3c_targ_trx_txd_t txd_data_out[NumTargets];
  // Direct Read CCCs.
  // - to ensure that there is no skew amongst the targets we use a single synchronizer and a wider
  //   data bus.
  logic txc_toggle_out;
  logic txc_toggle_in;
  i3c_targ_trx_txc_t txc_data_out;

  // Arbitration request to the transceiver.
  logic arb_toggle_out, arb_toggle_in;
  i3c_targ_trx_arb_t arb_data;

  // Received data from the transceiver.
  logic trx_rvalid, trx_rready;
  i3c_targ_trx_rxd_t trx_rxd;

  // Error events reported by the Target core.
  logic async_evt_ovl;
  logic rx_buffer_ovl;
  logic rx_desc_ovl;
  logic transfer_err;
  logic transfer_aborted;

  // Target Core state machine.
  i3c_target_fsm #(
    .NumTargets(NumTargets),
    .DataWidth (DataWidth),
    .FIFODepthW(FIFODepthW),
    .TargetExt (TargetExt)
  ) u_target_fsm (
    .clk_i                (clk_i),
    .rst_ni               (rst_ni),

    // Reset for transceiver logic.
    .trx_rst_ni           (trx_rst_ni),

    // Control inputs.
    .enable_i             (enable_i),
    .sw_reset_i           (sw_reset_i),
    .async_evt_rst_i      (async_evt_rst_i),

    // Configuration.
    .reg2hw_i             (reg2hw_i),
    .stby_cr_enable_init_i(stby_cr_enable_init_i),
    .stby_cr_cr_req_send_i(stby_cr_cr_req_send_i),
    .stby_cr_dcr_i        (stby_cr_dcr_i),
    .stby_cr_bcr_i        (stby_cr_bcr_i),
    .stby_cr_pid_i        (stby_cr_pid_i),
    .rstact_i             (rstact_i),
    // Blocked device addresses.
    .addr_blocked_i       (addr_blocked_i),
    .mask_blocked_i       (mask_blocked_i),

    // Status information.
    .dynaddr_de_o         (dynaddr_de_o),
    .dynaddr_valid_d_o    (dynaddr_valid_d_o),
    .dynaddr_d_o          (dynaddr_d_o),
    .virt_targ_det_o      (virt_targ_det_o),
    .mwl_de_o             (mwl_de_o),
    .mrl_de_o             (mrl_de_o),
    .ibi_de_o             (ibi_de_o),
    .mwl_d_o              (mwl_d_o),
    .mrl_d_o              (mrl_d_o),
    .ibi_d_o              (ibi_d_o),
    .endis_event_o        (endis_event_o),
    .rstact_de_o          (rstact_de_o),
    .rstact_d_o           (rstact_d_o),
    .grp_addr_de_o        (grp_addr_de_o),
    .grp_targ_de_o        (grp_targ_de_o),
    .grp_addr_d_o         (grp_addr_d_o),
    .grp_targ_d_o         (grp_targ_d_o),
    .act_state_de_o       (act_state_de_o),
    .act_state_d_o        (act_state_d_o),
    .endxfer_cand_de_o    (endxfer_cand_de_o),
    .endxfer_cand_d_o     (endxfer_cand_d_o),
    .endxfer_de_o         (endxfer_de_o),
    .endxfer_d_o          (endxfer_d_o),
    .vend_test_mode_o     (vend_test_mode_o),
    .protocol_error_o     (protocol_error_o),

    // Bus signals, already synchronized to the IP clock domain.
    .scl_i                (scl_i),
    .sda_i                (sda_i),
    // Bus status signals.
    .bus_avail_i          (bus_avail_i),
    .bus_idle_i           (bus_idle_i),

    // Standby Controller enabled?
    .stby_cr_enabled_i    (stby_cr_enabled_i),

    // Target device descriptions.
    .targ_dev_i           (targ_dev),

    // Start request to the transceiver.
    .sreq_sda_od_en_o     (sreq_sda_od_en_o),
    .sreq_sda_o           (sreq_sda_o),

    // Status indications from the transceiver.
    .rep_start_det_i      (rep_start_det),
    .stop_det_i           (stop_det),
    .ddr_mode_i           (ddr_mode_sync),

    // Transmission from Virtual Target(s) suspended.
    .suspend_tx_o         (suspend_tx_o),
    // IBI Transmission suspended.
    .ibi_suspend_tx_o     (ibi_suspend_tx_o),
    // Clear the Abort status when transmission is resumed.
    .abort_clr_o          (abort_clr_o),
    .ibi_abort_clr_o      (ibi_abort_clr_o),

    // Transmission Descriptor access.
    .tx_desc_rready_o     (tx_desc_rready_o),
    .tx_desc_rvalid_i     (tx_desc_rvalid_i),
    .tx_desc_rdata_i      (tx_desc_rdata_i),
    .tx_desc_rused_i      (tx_desc_rused_i),
    .tx_desc_ravail_i     (tx_desc_ravail_i),

    // Reception Descriptor access.
    .rx_desc_wvalid_o     (rx_desc_wvalid_o),
    .rx_desc_wdata_o      (rx_desc_wdata_o),
    .rx_desc_wready_i     (rx_desc_wready_i),
    .rx_desc_wused_i      (rx_desc_wused_i),
    .rx_desc_wfull_i      (rx_desc_wfull_i),

    // In-Band Interrupt Descriptor access.
    .ibi_desc_rready_o    (ibi_desc_rready_o),
    .ibi_desc_rvalid_i    (ibi_desc_rvalid_i),
    .ibi_desc_rdata_i     (ibi_desc_rdata_i),

    // Buffer reading.
    .buf_rready_o         (buf_rready_o),
    .buf_rvalid_i         (buf_rvalid_i),
    .buf_rdata_i          (buf_rdata_i),
    .buf_rempty_i         (buf_rempty_i),
    .buf_rused_i          (buf_rused_i),

    // In-Band Interrupt reading.
    .ibi_rready_o         (ibi_rready_o),
    .ibi_rvalid_i         (ibi_rvalid_i),
    .ibi_rdata_i          (ibi_rdata_i),
    .ibi_rempty_i         (ibi_rempty_i),
    .ibi_rused_i          (ibi_rused_i),

    // Requests/status information to the transceiver.
    .txd_toggle_o         (txd_toggle_out),
    .txd_toggle_i         (txd_toggle_in),
    .txd_data_o           (txd_data_out),

    // Transmit data for Direct Read CCCs.
    .txc_toggle_o         (txc_toggle_out),
    .txc_toggle_i         (txc_toggle_in),
    .txc_data_o           (txc_data_out),

    // Arbitration requests to the transceiver.
    .arb_toggle_o         (arb_toggle_out),
    .arb_toggle_i         (arb_toggle_in),
    .arb_data_o           (arb_data),

    // Response from the transceiver logic.
    .trx_rvalid_i         (trx_rvalid),
    .trx_rxd_i            (trx_rxd),
    .trx_rready_o         (trx_rready),

    // Buffer writing.
    .buf_wvalid_o         (buf_wvalid_o),
    .buf_wdata_o          (buf_wdata_o),
    .buf_wready_i         (buf_wready_i),
    .buf_wavail_i         (buf_wavail_i),

    // Asynchronous Event Queue.
    .async_wvalid_o       (async_wvalid_o),
    .async_wdata_o        (async_wdata_o),
    .async_wready_i       (async_wready_i),

    // Setting of Standby Controller Dynamic Address.
    .stby_cr_dynaddr_de_o (stby_cr_dynaddr_de_o),
    .stby_cr_dynaddr_d_o  (stby_cr_dynaddr_d_o),

    // Broadcast CCCs received in Standby Controller Mode.
    .stby_bcst_wvalid_o   (stby_bcst_wvalid_o),
    .stby_bcst_wdata_o    (stby_bcst_wdata_o),
    .stby_bcst_wready_i   (stby_bcst_wready_i),

    // Error events.
    .async_evt_ovl_o      (async_evt_ovl),
    .rx_buffer_ovl_o      (rx_buffer_ovl),
    .rx_desc_ovl_o        (rx_desc_ovl),
    .transfer_err_o       (transfer_err),
    .transfer_aborted_o   (transfer_aborted),

    // Data sink status signals.
    .sink_dwords_left_o   (sink_dwords_left_o),
    .sink_active_o        (sink_active_o),
    .sink_error_o         (sink_error_o),

    // Extension hardware.
    .ext_present_o        (ext_present_o),
    .ext_info_o           (ext_info_o),

    // Register interface.
    .ext_reg2hw_i         (ext_reg2hw_i),
    .ext_hw2reg_o         (ext_hw2reg_o),

    // Diagnostic visibility into Target core state.
    .fsm_state_o          (fsm_state_o)
  );

  // Present Transmit data and status information for each supported target.
  for (genvar t = 0; t < NumTargets; t++) begin : gen_targ_txd_sync
    // Private Transfers.
    i3c_sync_data #(
      .Width         ($bits(i3c_targ_trx_txd_t)),
      .EnSrcToggleOut(1)
    ) u_targ_txd_sync (
      // IP block domain.
      .clk_src_i   (clk_i),
      .rst_src_ni  (trx_rst_ni),
      .src_toggle_i(txd_toggle_out[t]),
      .src_toggle_o(txd_toggle_in[t]),
      .src_data_i  (txd_data_out[t]),

      // SCL-clocked domain.
      .clk_dst_i     (scl_ni),
      .rst_dst_ni    (trx_rst_ni),
      .dst_valid_o   (trx_dvalid_o[t]),
      .dst_ready_i   (trx_dready_i[t]),
      .dst_data_o    (trx_dreq_o[t]),
      .dst_dataloss_o()
    );
  end

  // Direct Read CCCs; all targets share a single synchronizer so that there is no skew amongst
  // the targets, complicating the FSM/CCC logic.
  i3c_sync_data #(
    .Width         ($bits(i3c_targ_trx_txc_t)),
    .EnSrcToggleOut(1)
  ) u_targ_txc_sync (
    // IP block domain.
    .clk_src_i   (clk_i),
    .rst_src_ni  (trx_rst_ni),
    .src_toggle_i(txc_toggle_out),
    .src_toggle_o(txc_toggle_in),
    .src_data_i  (txc_data_out),

    // SCL-clocked domain.
    .clk_dst_i     (scl_ni),
    .rst_dst_ni    (trx_rst_ni),
    .dst_valid_o   (trx_ctvalid_o),
    .dst_ready_i   (trx_ctready_i),
    .dst_data_o    (trx_ctreq_o),
    .dst_dataloss_o()
  );

  // Send arbitration requests to the transceiver.
  i3c_sync_data #(
    .Width         ($bits(i3c_targ_trx_arb_t)),
    .EnSrcToggleOut(1)
  ) u_arb_sync (
    // IP block domain.
    .clk_src_i   (clk_i),
    .rst_src_ni  (trx_rst_ni),
    .src_toggle_i(arb_toggle_out),
    .src_toggle_o(arb_toggle_in),
    .src_data_i  (arb_data),

    // SCL-clocked domain.
    .clk_dst_i     (scl_ni),
    .rst_dst_ni    (trx_rst_ni),
    .dst_valid_o   (trx_avalid_o),
    .dst_ready_i   (trx_aready_i),
    .dst_data_o    (trx_areq_o),
    .dst_dataloss_o()
  );

  // Synchronize the received data into the IP clock domain.
  i3c_sync_data #(
    .Width($bits(i3c_targ_trx_rxd_t))
  ) u_trx_rxd_sync (
    // SCL-clocked domain.
    .clk_src_i   (1'b0),  // Not used.
    .rst_src_ni  (1'b1),  // Not used.
    .src_toggle_i(trx_rtoggle_i),
    .src_toggle_o(),  // Not used.
    .src_data_i  (trx_rxd_i),

    // IP block domain.
    .clk_dst_i     (clk_i),
    .rst_dst_ni    (trx_rst_ni),
    .dst_valid_o   (trx_rvalid),
    .dst_ready_i   (trx_rready),
    .dst_data_o    (trx_rxd),
    .dst_dataloss_o()
  );

  // Interrupt generation.
  // Gate all interrupts that depend on a threshold value with the threshold value being non-zero.
  always_comb begin
    // Reception uses a single buffer for all Targets.
    intr_o = '0;  // Note: this provides drivers for non-extant Virtual Targets.
    intr_o.rx_desc_ready   = |reg2hw_i.targ_queue_thld_ctrl.rx_desc_thld.q &&
                             (rx_desc_wused_i >= reg2hw_i.targ_queue_thld_ctrl.rx_desc_thld.q);
    intr_o.ibi_status_thld = |reg2hw_i.targ_queue_thld_ctrl.ibi_status_thld.q &&
                             (ibi_desc_ravail_i >= reg2hw_i.targ_queue_thld_ctrl.ibi_status_thld.q);
    intr_o.async_evt_ready = !async_empty_i;  // TODO: Need to reconsider if CCC becomes multi-desc?
    intr_o.transfer_abort  = transfer_aborted;
    intr_o.transfer_err    = transfer_err;
    // TODO: Make a separate interrupt for rx_desc_ovl.
    intr_o.rx_buffer_ovl   = rx_buffer_ovl | rx_desc_ovl;
    intr_o.async_evt_ovl   = async_evt_ovl;

    // Transmission requires per-Target buffers.
    for (int unsigned t = 0; t < NumTargets; t++) begin
      intr_o.tx_thld[t] = |reg2hw_i.targ_tx_thld_ctrl[t].tx_buf_free_thld.q &&
        (buf_ravail_i[t] >= reg2hw_i.targ_tx_thld_ctrl[t].tx_buf_free_thld.q);
      intr_o.tx_desc_ready[t] = |reg2hw_i.targ_tx_thld_ctrl[t].tx_desc_empty_thld.q &&
        (tx_desc_ravail_i[t] >= reg2hw_i.targ_tx_thld_ctrl[t].tx_desc_empty_thld.q);
    end

    // Raise an interrupt to software when any of the Target Error counts is non-zero.
    intr_o.te = |{reg2hw_i.targ_error.dbr.q, reg2hw_i.targ_error.te6.q,
                  reg2hw_i.targ_error.te5.q, reg2hw_i.targ_error.te4.q,
                  reg2hw_i.targ_error.te3.q, reg2hw_i.targ_error.te2.q,
                  reg2hw_i.targ_error.te1.q, reg2hw_i.targ_error.te0.q};
  end

  // TODO: When we have logic for detecting TE0/TE1 we are required to enable the
  // HDR Exit Pattern Detector then too.
  // TODO: This may need to come from the transceiver.
  assign hdr_exit_det_en_o = 1'b1;

  // Clear Hot-Join request once it has been acknowledged by the Active Controller.
  // TODO: We cannot yet issue a Hot-Join request.
  assign hj_request_clear_o = 1'b0;

  // TTI Data Structures that must fit into one buffer data word (currently fixed to 32b).
  if ($bits(i3c_tti_tx_desc_t) != DataWidth)    $fatal(1, "TTI Tx Descriptor has incorrect size.");
  if ($bits(i3c_tti_rx_desc_t) != DataWidth)    $fatal(1, "TTI Rx Descriptor has incorrect size.");
  if ($bits(i3c_tti_ibi_status_t) != DataWidth) $fatal(1, "TTI IBI Status Descriptor has incorrect size.");

  // Assertions.
  `ASSERT_INIT(NumTargetsLegal, NumTargets <= MaxTargets)

endmodule
