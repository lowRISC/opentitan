// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I3C Controller core.
module i3c_controller
  import i3c_controller_pkg::*;
  import i3c_fifo_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
  import prim_ram_1p_pkg::*;
#(
  parameter int unsigned ClkFreq       = 50_000_000,
  parameter bit          PrimaryCtrl   = 1'b1,
  parameter bit          SecondaryCtrl = 1'b0,
  parameter int unsigned DataWidth     = 32,
  parameter int unsigned FIFODepthW    = i3c_fifo_pkg::DepthW,
  parameter int unsigned NumDATEntries = i3c_pkg::NumDATEntries,
  parameter int unsigned NumDCTEntries = i3c_pkg::NumDCTEntries,

  // Derived parameters.
  localparam int unsigned DATAddrW = $clog2(NumDATEntries),
  localparam int unsigned DCTAddrW = $clog2(NumDCTEntries)
) (
  // Clock and reset for system interface.
  input                       clk_i,
  input                       rst_ni,

  // Control inputs.
  input                       sw_reset_i,
  input                       fifo_rst_i[FIFO_Count],
  input                       stby_cr_enabled_i,

  // Configuration settings.
  input  i3c_reg2hw_t         reg2hw_i,
  input                       dct_idx_qe_i,
  input        [DCTAddrW-1:0] dct_idx_q_i,

  // Blocked device addresses.
  input                 [6:0] addr_blocked_i[NumBlocked],
  input                 [6:0] mask_blocked_i[NumBlocked],

  // State information, presented via HCI.
  output                      enabled_o,
  output                      ac_current_own_o,
  output       [DCTAddrW-1:0] dct_idx_o,
  output         hc_control_t hc_control_o,

  // Command Queue access.
  output                      cmd_desc_rready_o,
  input                       cmd_desc_rvalid_i,
  input       [DataWidth-1:0] cmd_desc_rdata_i,
  input        [FIFODepthW:0] cmd_desc_ravail_i,

  // Response Queue access.
  output                      rsp_desc_wvalid_o,
  output      [DataWidth-1:0] rsp_desc_wdata_o,
  input                       rsp_desc_wready_i,
  input        [FIFODepthW:0] rsp_desc_wused_i,
  input                       rsp_desc_wfull_i,

  // IBI Queue access.
  output                      ibi_data_wvalid_o,
  output      [DataWidth-1:0] ibi_data_wdata_o,
  input                       ibi_data_wready_i,
  input                       ibi_data_wfull_i,

  // IBI Status Descriptor FIFO access.
  output                      ibi_stat_wvalid_o,
  output      [DataWidth-1:0] ibi_stat_wdata_o,
  input                       ibi_stat_wready_i,
  input        [FIFODepthW:0] ibi_stat_wused_i,
  input                       ibi_stat_wfull_i,

  // HCI Device Address Table interface.
  input                       sw_dat_req_i,
  output                      sw_dat_gnt_o,
  input                       sw_dat_we_i,
  input          [DATAddrW:0] sw_dat_addr_i,
  input       [DataWidth-1:0] sw_dat_wdata_i,
  output                      sw_dat_rvalid_o,
  output      [DataWidth-1:0] sw_dat_rdata_o,

  // HCI Device Characteristics Table interface.
  input                       sw_dct_req_i,
  output                      sw_dct_gnt_o,
  input                       sw_dct_we_i,
  input        [DCTAddrW+1:0] sw_dct_addr_i,
  input       [DataWidth-1:0] sw_dct_wdata_i,
  output                      sw_dct_rvalid_o,
  output      [DataWidth-1:0] sw_dct_rdata_o,

  // Interrupt signals.
  output i3c_hc_intr_t        intr_hc_o,
  output i3c_pio_intr_t       intr_pio_o,
  output i3c_stby_cr_intr_t   intr_stby_cr_o,

  // Reading from Tx Buffer.
  output                      txbuf_rready_o,
  input                       txbuf_rvalid_i,
  input       [DataWidth-1:0] txbuf_rdata_i,
  input                       txbuf_rempty_i,
  input        [FIFODepthW:0] txbuf_rused_i,
  input        [FIFODepthW:0] txbuf_ravail_i,

  // Writing to Rx Buffer.
  output                      rxbuf_wvalid_o,
  output      [DataWidth-1:0] rxbuf_wdata_o,
  input                       rxbuf_wready_i,
  input        [FIFODepthW:0] rxbuf_wused_i,
  input                       rxbuf_wfull_i,
  input        [FIFODepthW:0] rxbuf_wavail_i,

  // Broadcast CCCs received in Standby Controller mode.
  input                       stby_bcst_wvalid_i,
  input       [DataWidth-1:0] stby_bcst_wdata_i,
  output                      stby_bcst_wready_o,

  // Start request signaling from Targets.
  input                       trx_sreq_i,

  // Timing parameters; Target- and transfer-invariant.
  output         [TmCycW-1:0] tcas_d2_o,
  output         [TmCycW-1:0] tcbp_d2_o,
  output         [TmCycW-1:0] todch_d2_o,
  output         [TmCycW-1:0] todcl_d2_o,
  output                      enable_hc_scl_o,

  // Retrying of NACKed commands.
  output                      cmd_nacked_o,
  input                       cmd_retry_i,

  // Request to the transceiver.
  output                      trx_dvalid_o,
  input                       trx_dready_i,
  output i3c_ctrl_trx_req_t   trx_dreq_o,

  // Arbitration requests from the transceiver.
  input                       trx_avalid_i,
  input  i3c_ctrl_trx_arb_t   trx_arb_i,
  output                      trx_aready_o,
  output                      trx_arb_nack_o,

  // Read data from the transceiver.
  input                       trx_rdvalid_i,
  input  i3c_ctrl_trx_rdata_t trx_rdata_i,

  // Response from the transceiver.
  input                       trx_rvalid_i,
  output                      trx_rready_o,
  input  i3c_ctrl_trx_rsp_t   trx_rsp_i,

  // Debug status information.
  output                [3:0] cmd_tid_o,
  output                [5:0] bcl_tfr_ststat_o,
  output                [7:0] ce2_error_cnt_o,
  output                [3:0] ctrl_error_o,

  // DFT-related signals.
  input  ram_1p_cfg_req_t     dat_cfg_i,
  output ram_1p_cfg_rsp_t     dat_cfg_o,
  input  ram_1p_cfg_req_t     dct_cfg_i,
  output ram_1p_cfg_rsp_t     dct_cfg_o
);

  import i3c_consts_pkg::*;

  // Number of byte write strobes per DCT entry.
  localparam int unsigned DCTMaskW = ($bits(i3c_dct_mem_t) + 7) / 8;

  // Access to Device Address Table (DAT).
  logic                dat_re;
  logic [DATAddrW-1:0] dat_idx;
  i3c_dat_mem_t        dat_rdata;

  // Access to Device Characteristics Table (DCT).
  logic                dct_we;
  logic [DCTMaskW-1:0] dct_wmask;
  i3c_dct_mem_t        dct_wdata;

  // Controller-global state (Disabled, Suspended|Halted, Aborted, Running...)
  logic enabled;
  logic aborted;           // Acknowledgement by the FSM of the Abort request.
  logic transfer_aborted;  // One or more transfers had to be aborted in handling the request.
  // Is the Controller FSM inactive; nothing in progress?
  logic inactive;
  // Command processing suspending due to an error?
  logic suspending;
  // Enable signal that encompasses Standby Controller mode too.
  // - most of the Controller logic is inactive in this case, but the IBI-related logic is still
  //   required for notification of Broadcast CCCs.
  logic enabled_stby;

  // Global state of the Controller.
  // - Enabled/Disabled.
  // - Suspend/Resume.
  i3c_ctrl_gstate_e gstate;

  i3c_controller_state u_hc_state (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),

    // Control inputs.
    .sw_reset_i  (sw_reset_i),

    // Configuration settings; software-initiated state changes.
    .reg2hw_i    (reg2hw_i),

    // Indication that the Controller logic has become inactive and may be gated off.
    .inactive_i  (inactive),
    // Command processing suspending due to an error?
    .suspending_i(suspending),
    // Status signal indicating that the Controller logic has aborted.
    .aborted_i   (aborted),

    // Current global state.
    .gstate_o    (gstate),

    // Global enabled/disabled signal used for clock-gating.
    .enabled_o   (enabled),

    // Register state presented to the HCI.
    .hc_control_o(hc_control_o)
  );

  // Exported global state and clock-gating enable.
  assign enabled_o = enabled;

  // Controller enable that includes Standby Controller mode too.
  // - we must keep the IBI Queue and associated logic operational in Standby Controller mode, so
  //   that Broadcast CCC notifications can be presented to the software driver.
  // TODO: This may require refinement when Secondary/Standby Controller role is supported.
  assign enabled_stby = enabled | stby_cr_enabled_i;

  // Software writes to the DAT must update entries in the DAT cache; writes are narrower than the
  // DAT entry, but fortunately the required information all lies within a single bus word (the
  // first within the DAT entry).
  //
  // Note: The `i3c_dat` memory will grant the software write only when the DAT is _not_ being read
  // by the Controller FSM hardware.
  i3c_datc_wdata_t sw_datc_wdata;
  i3c_dat_entry_t sw_dat_entry;
  wire sw_datc_we = &{sw_dat_req_i, sw_dat_gnt_o, sw_dat_we_i, !sw_dat_addr_i[0]};  // Lowest word.
  wire [DATAddrW-1:0] sw_datc_widx = sw_dat_addr_i[DATAddrW:1];  // Entry index.
  assign sw_dat_entry = i3c_dat_entry_t'({2{sw_dat_wdata_i}});   // Reinterpret write data.
  assign sw_datc_wdata.dyn_addr    = sw_dat_entry.dynamic_address;
  assign sw_datc_wdata.ibi_payload = sw_dat_entry.ibi_payload;
  assign sw_datc_wdata.ibi_reject  = sw_dat_entry.ibi_reject;
  assign sw_datc_wdata.crr_reject  = sw_dat_entry.crr_reject;

  // Core state machine for Command/Response processing.
  i3c_controller_fsm #(
    .ClkFreq            (ClkFreq),
    .DataWidth          (DataWidth),
    .FIFODepthW         (FIFODepthW),
    .NumDATEntries      (NumDATEntries),
    .NumDCTEntries      (NumDCTEntries)
  ) u_ctrl_fsm (
    .clk_i             (clk_i),
    .rst_ni            (rst_ni),

    // Control inputs.
    .enable_i          (enabled),
    .enable_stby_i     (enabled_stby),
    .sw_reset_i        (sw_reset_i),
    .fifo_rst_i        (fifo_rst_i),
    .gstate_i          (gstate),

    // Status outputs.
    .inactive_o        (inactive),
    .suspending_o      (suspending),
    .aborted_o         (aborted),
    .transfer_aborted_o(transfer_aborted),

    // Configuration.
    .reg2hw_i          (reg2hw_i),
    .hc_control_i      (hc_control_o),

    // Software writes to the current DCT index.
    .dct_idx_qe_i      (dct_idx_qe_i),
    .dct_idx_q_i       (dct_idx_q_i),

    // Blocked device addresses.
    .addr_blocked_i    (addr_blocked_i),
    .mask_blocked_i    (mask_blocked_i),

    // Software writes to the DAT must update the DAT cache.
    .sw_datc_we_i      (sw_datc_we),
    .sw_datc_widx_i    (sw_datc_widx),
    .sw_datc_wdata_i   (sw_datc_wdata),

    // Reads from Device Address Table (DAT).
    .dat_re_o          (dat_re),
    .dat_idx_o         (dat_idx),
    .dat_rdata_i       (dat_rdata),

    // Writes to Device Characteristics Table (DCT).
    .dct_we_o          (dct_we),
    .dct_idx_o         (dct_idx_o),
    .dct_wmask_o       (dct_wmask),
    .dct_wdata_o       (dct_wdata),

    // Reads from Command Queue.
    .cmd_desc_rready_o (cmd_desc_rready_o),
    .cmd_desc_rvalid_i (cmd_desc_rvalid_i),
    .cmd_desc_rdata_i  (cmd_desc_rdata_i),

    // Writes to Response Queue.
    .rsp_desc_wvalid_o (rsp_desc_wvalid_o),
    .rsp_desc_wdata_o  (rsp_desc_wdata_o),
    .rsp_desc_wready_i (rsp_desc_wready_i),
    .rsp_desc_wfull_i  (rsp_desc_wfull_i),

    // Reads from Tx Data Buffer.
    .txbuf_rready_o    (txbuf_rready_o),
    .txbuf_rvalid_i    (txbuf_rvalid_i),
    .txbuf_rdata_i     (txbuf_rdata_i),
    .txbuf_rempty_i    (txbuf_rempty_i),
    .txbuf_rused_i     (txbuf_rused_i),

    // Writes to Rx Data Buffer.
    .rxbuf_wvalid_o    (rxbuf_wvalid_o),
    .rxbuf_wdata_o     (rxbuf_wdata_o),
    .rxbuf_wready_i    (rxbuf_wready_i),
    .rxbuf_wfull_i     (rxbuf_wfull_i),
    .rxbuf_wavail_i    (rxbuf_wavail_i),

    // Writes to In-Band Interrupt Queue.
    .ibi_data_wvalid_o (ibi_data_wvalid_o),
    .ibi_data_wdata_o  (ibi_data_wdata_o),
    .ibi_data_wready_i (ibi_data_wready_i),
    .ibi_data_wfull_i  (ibi_data_wfull_i),

    // Write to IBI Status Descriptor FIFO.
    .ibi_stat_wvalid_o (ibi_stat_wvalid_o),
    .ibi_stat_wdata_o  (ibi_stat_wdata_o),
    .ibi_stat_wready_i (ibi_stat_wready_i),
    .ibi_stat_wfull_i  (ibi_stat_wfull_i),

    // Broadcast CCCs received in Standby Controller mode.
    .stby_bcst_wvalid_i(stby_bcst_wvalid_i),
    .stby_bcst_wdata_i (stby_bcst_wdata_i),
    .stby_bcst_wready_o(stby_bcst_wready_o),

    // Start request signaling from Targets.
    .trx_sreq_i        (trx_sreq_i),

    // Timing parameterss; target- and transfer-invariant.
    .tcas_d2_o         (tcas_d2_o),
    .tcbp_d2_o         (tcbp_d2_o),
    .todch_d2_o        (todch_d2_o),
    .todcl_d2_o        (todcl_d2_o),

    // Configuration signals to the transceiver logic.
    .enable_hc_scl_o   (enable_hc_scl_o),

    // Retrying of NACKed commands.
    .cmd_nacked_o      (cmd_nacked_o),
    .cmd_retry_i       (cmd_retry_i),

    // Request to the transceiver.
    .trx_dvalid_o      (trx_dvalid_o),
    .trx_dready_i      (trx_dready_i),
    .trx_dreq_o        (trx_dreq_o),

    // Arbitration requests from the transceiver.
    .trx_avalid_i      (trx_avalid_i),
    .trx_arb_i         (trx_arb_i),
    .trx_aready_o      (trx_aready_o),
    .trx_arb_nack_o    (trx_arb_nack_o),

    // Read data from the transceiver.
    .trx_rdvalid_i     (trx_rdvalid_i),
    .trx_rdata_i       (trx_rdata_i),

    // Response from the transceiver.
    .trx_rvalid_i      (trx_rvalid_i),
    .trx_rready_o      (trx_rready_o),
    .trx_rsp_i         (trx_rsp_i),

    // CE[3:0] error conditions (Table 44).
    .ctrl_error_o      (ctrl_error_o),

    // Debug extended capability.
    .bcl_tfr_ststat_o  (bcl_tfr_ststat_o),
    .cmd_tid_o         (cmd_tid_o)
  );

  // Device Address Table (HCI 8.1).
  // - contains information about the currently-addressable devices on the I3C bus.
  // - read only from hardware, but accessed regularly as part of Command processing.
  // - the host driver ensures that the required information is available before issuing
  //   the commands.
  i3c_dat #(
    .DataWidth      (DataWidth),
    .NumDATEntries  (NumDATEntries)
  ) u_dat (
    .clk_i,
    .rst_ni,

    // Hardware interface.
    .dat_re_i   (dat_re),
    .dat_idx_i  (dat_idx),
    .dat_rdata_o(dat_rdata),

    // HCI Device Address Table interface.
    .sw_dat_req_i,
    .sw_dat_gnt_o,
    .sw_dat_we_i,
    .sw_dat_addr_i,
    .sw_dat_wdata_i,
    .sw_dat_rvalid_o,
    .sw_dat_rdata_o,

    .dat_cfg_i,
    .dat_cfg_o
  );

  // Device Characteristics Table (HCI 8.2).
  // - returns the characteristics of the devices that have been configured in the current
  //   Dynamic Address Allocation operation.
  // - write only from hardware.
  i3c_dct #(
    .DataWidth      (DataWidth),
    .NumDCTEntries  (NumDCTEntries)
  ) u_dct (
    .clk_i,
    .rst_ni,

    // Hardware interface.
    .dct_we_i   (dct_we),
    .dct_idx_i  (dct_idx_o),
    .dct_wmask_i(dct_wmask),
    .dct_wdata_i(dct_wdata),

    // HCI Device Characteristics Table interface.
    .sw_dct_req_i,
    .sw_dct_gnt_o,
    .sw_dct_we_i,
    .sw_dct_addr_i,
    .sw_dct_wdata_i,
    .sw_dct_rvalid_o,
    .sw_dct_rdata_o,

    .dct_cfg_i,
    .dct_cfg_o
  );

  // TODO: This will need revisiting when Standby Controller operation is fully implemented.
  assign ac_current_own_o = enabled;

  // Interrupt-generating thresholds on Rx and Tx Data Buffers.
  // HCI Table 42 footnotes declare that thse thresholds must be within the sizes of the buffers.
  logic rx_thld, tx_thld;
  assign rx_thld = |(rxbuf_wused_i[FIFODepthW:1]  >> reg2hw_i.data_buffer_thld_ctrl.rx_buf_thld.q);
  assign tx_thld = |(txbuf_ravail_i[FIFODepthW:1] >> reg2hw_i.data_buffer_thld_ctrl.tx_buf_thld.q);

  // HCI Table 41 declares that the programmed Cmd/Resp thresholds shall be clamped to the queue
  // sizes before being used in the generation of Command/Response queue status interrupts.
  logic [7:0] cmd_empty_buf_thld;
  logic [7:0] resp_buf_thld;
  always_comb begin
    // Command Queue threshold and size are both in terms of _entries_, each entry being two DWORDs.
    cmd_empty_buf_thld = reg2hw_i.queue_thld_ctrl.cmd_empty_buf_thld.q;
    if (cmd_empty_buf_thld > reg2hw_i.command_queue_config.size_val.q) begin
      cmd_empty_buf_thld = reg2hw_i.command_queue_config.size_val.q;
    end
    // Note: we know that we declare `ALT_RESP_QUEUE_EN` and that the Response Queue size is
    //       described separately in `ALT_QUEUE_SIZE`.
    resp_buf_thld = reg2hw_i.queue_thld_ctrl.resp_buf_thld.q;
    if (resp_buf_thld > reg2hw_i.response_queue_config.size_val.q) begin
      resp_buf_thld = reg2hw_i.response_queue_config.size_val.q;
    end
  end

  // Interrupt generation.
  always_comb begin
    intr_hc_o = '0;  // TODO: Error-related interrupts yet to be implemented; no scheduled cmds.
    intr_pio_o = '0;
    intr_stby_cr_o = '0;  // TODO: Standby Controller role deferred.

    // FIFO-state threshold interrupt signals.
    // Note: These threshold values are programmed as entry counts; for the Command Queue an entry
    //       is equivalent to 2 DWORDs.
    // TODO: Transfer errors and aborts are not yet properly reported here; placeholder drivers.
    intr_pio_o.transfer_err    = suspending;
    intr_pio_o.transfer_abort  = transfer_aborted;
    intr_pio_o.resp_ready      = |reg2hw_i.queue_thld_ctrl.resp_buf_thld.q &&  // Field valid?
                                 (rsp_desc_wused_i >= resp_buf_thld);
    intr_pio_o.cmd_queue_ready = |reg2hw_i.queue_thld_ctrl.cmd_empty_buf_thld.q &&  // Field valid?
                                 (cmd_desc_ravail_i[FIFODepthW:1] >= cmd_empty_buf_thld);
    // Note that this is comparing the number of IBI Status Descriptors.
    intr_pio_o.ibi_status_thld = |reg2hw_i.queue_thld_ctrl.ibi_status_thld.q &&  // Field valid?
             (ibi_stat_wused_i >= reg2hw_i.queue_thld_ctrl.ibi_status_thld.q);
    intr_pio_o.rx_thld = rx_thld;
    intr_pio_o.tx_thld = tx_thld;
  end

  // Controller Error Counters (HCI 7.7.7.4).
  logic [7:0] ce2_error_cnt;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) ce2_error_cnt <= 'b0;  // CE2 (4.3.8.2.3) count.
    else if (reg2hw_i.mx_error_counters.re | ctrl_error_o[2]) begin
      // Reading from the CE2_ERROR_COUNT field clears this saturating counter of CE2 errors.
      // - the sw read data path is combinational w.r.t. 're' assertion; cleared in the next cycle.
      // - count CE2 events unless the counter is already saturated and not being cleared.
      ce2_error_cnt <= (reg2hw_i.mx_error_counters.re ? 'b0 : ce2_error_cnt) +
                      ((reg2hw_i.mx_error_counters.re | ~&ce2_error_cnt) & ctrl_error_o[2]);
    end
  end
  assign ce2_error_cnt_o = ce2_error_cnt;

  // Compile-time checks of the basic I3C structures to detect inadvertent changes.
  // HCI specification tables (8.1 and 8.2).
  if ($bits(i3c_dat_entry_t) != 64)  $fatal(1, "DAT Table Entry has incorrect size.");
  if ($bits(i3c_dct_entry_t) != 128) $fatal(1, "DCT Table Entry has incorrect size.");
  // Command, Response and IBI Status Descriptors.
  if ($bits(i3c_xfer_cmd_imm_t) != 64)         $fatal(1, "Immediate Command has incorrect size.");
  if ($bits(i3c_xfer_cmd_reg_t) != 64)         $fatal(1, "Regular Command has incorrect size.");
  if ($bits(i3c_xfer_cmd_combo_t) != 64)       $fatal(1, "Combo Command has incorrect size.");
  if ($bits(i3c_xfer_cmd_addr_assgn_t) != 64)  $fatal(1, "Addr Assign Command has incorrect size.");
  if ($bits(i3c_xfer_cmd_intern_ctrl_t) != 64) $fatal(1, "Intn Ctrl Command has incorrect size.");
  if ($bits(i3c_xfer_rsp_t) != 32)             $fatal(1, "Response Descriptor has incorrect size.");
  if ($bits(i3c_ibi_status_t) != 32)           $fatal(1, "IBI Descriptor has incorrect size.");

endmodule
