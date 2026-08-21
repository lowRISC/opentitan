// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Target Core state machine for responding to Common Command Codes and Private Reads/Writes.
// This is also responsible for issuing In-Band Interrupts onto the I3C bus, and Asynchronous Events
// back to the software.
module i3c_target_fsm
  import i3c_consts_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
  import i3c_target_pkg::*;
  import i3c_targ_ext_pkg::*;
#(
  // Number of target(s) presented simultaneously on the I3C bus, including the Standby Controller.
  parameter int unsigned NumTargets = 2,
  parameter int unsigned DataWidth  = 32,
  parameter int unsigned FIFODepthW = i3c_fifo_pkg::DepthW,
  parameter bit          TargetExt  = 1'b0
) (
  input                     clk_i,
  input                     rst_ni,

  // Reset for transceiver logic.
  input                     trx_rst_ni,

  // Control inputs.
  input                     enable_i,
  input                     sw_reset_i, // TODO: Not used/connected to all required flops.
  input                     async_evt_rst_i,

  // Configuration.
  input  i3c_reg2hw_t       reg2hw_i,
  input               [1:0] stby_cr_enable_init_i,
  input                     stby_cr_cr_req_send_i,
  input               [7:0] stby_cr_dcr_i,
  input               [7:0] stby_cr_bcr_i,
  input              [47:0] stby_cr_pid_i,
  input  i3c_rstact_e       rstact_i, // TODO: Currently unused
  // Blocked device addresses.
  // TODO: Both currently unused
  input               [6:0] addr_blocked_i[NumBlocked],
  input               [6:0] mask_blocked_i[NumBlocked],

  // Status information.
  output logic              virt_targ_det_o,
  // Updating configuration.
  output   [NumTargets-1:0] dynaddr_de_o,
  output                    dynaddr_valid_d_o,
  output              [6:0] dynaddr_d_o[NumTargets],
  output   [NumTargets-1:0] mwl_de_o,
  output   [NumTargets-1:0] mrl_de_o,
  output   [NumTargets-1:0] ibi_de_o,
  output             [15:0] mwl_d_o,
  output             [15:0] mrl_d_o,
  output              [7:0] ibi_d_o,
  output i3c_endis_event_t  endis_event_o,
  // Update the RSTACT in response to CCC.
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

  // Bus signals, already synchronized to the IP clock domain.
  input                     scl_i,
  input                     sda_i,
  // Bus status signals.
  // TODO: bus_avail_i currently unused
  input                     bus_avail_i,
  input                     bus_idle_i,

  // Standby Controller enabled?
  input                     stby_cr_enabled_i,

  // Target device descriptions.
  input  i3c_targ_dev_t     targ_dev_i[NumTargets],

  // Start request to the transceiver.
  // - SDA lowered to request Start signaling, and partial address phase.
  output                    sreq_sda_od_en_o,
  output                    sreq_sda_o,

  // Status indications from the transceiver.
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
  // TODO: rused/ravail below currently unused.
  input      [FIFODepthW:0] tx_desc_rused_i[NumTargets],
  input      [FIFODepthW:0] tx_desc_ravail_i[NumTargets],

  // Reception Descriptor access.
  output                    rx_desc_wvalid_o,
  output    [DataWidth-1:0] rx_desc_wdata_o,
  input                     rx_desc_wready_i,
  // TODO: wused/wfull below currently unused.
  input      [FIFODepthW:0] rx_desc_wused_i,
  input                     rx_desc_wfull_i,

  // In-Band Interrupt Descriptor access.
  output                    ibi_desc_rready_o,
  input                     ibi_desc_rvalid_i,
  input     [DataWidth-1:0] ibi_desc_rdata_i,

  // Buffer reading.
  output                    buf_rready_o[NumTargets],
  input                     buf_rvalid_i[NumTargets],
  input     [DataWidth-1:0] buf_rdata_i[NumTargets],
  input                     buf_rempty_i[NumTargets],
  input      [FIFODepthW:0] buf_rused_i[NumTargets],

  // In-Band Interrupt reading.
  output                    ibi_rready_o,
  input                     ibi_rvalid_i,
  input     [DataWidth-1:0] ibi_rdata_i,
  input                     ibi_rempty_i,
  // TODO: rused currently unused
  input      [FIFODepthW:0] ibi_rused_i,

  // Transmit data for Private Read transfers.
  output logic              txd_toggle_o[NumTargets],
  input                     txd_toggle_i[NumTargets],
  output i3c_targ_trx_txd_t txd_data_o[NumTargets],

  // Transmit data for Direct Read CCCs.
  output logic              txc_toggle_o,
  input                     txc_toggle_i,
  output i3c_targ_trx_txc_t txc_data_o,

  // Arbitration requests to the transceiver.
  output logic              arb_toggle_o,
  input                     arb_toggle_i,
  output i3c_targ_trx_arb_t arb_data_o,

  // Received data, from the transceiver logic; Private Write transfers and CCC handling.
  input                     trx_rvalid_i,
  input  i3c_targ_trx_rxd_t trx_rxd_i,
  output logic              trx_rready_o,

  // Buffer writing.
  output                    buf_wvalid_o,
  output    [DataWidth-1:0] buf_wdata_o,
  input                     buf_wready_i,
  input      [FIFODepthW:0] buf_wavail_i, // TODO: Currently unused.

  // Asynchronous Event Queue.
  output                    async_wvalid_o,
  output    [DataWidth-1:0] async_wdata_o,
  input                     async_wready_i,

  // Setting the Standby Controller Dynamic Address.
  output                    stby_cr_dynaddr_de_o,
  output              [7:0] stby_cr_dynaddr_d_o,  // Validity indicator in MSB.

  // Broadcast CCCs received in Standby Controller mode.
  output                    stby_bcst_wvalid_o,
  output    [DataWidth-1:0] stby_bcst_wdata_o,
  input                     stby_bcst_wready_i, // TODO: Currently unused.

  // Error events.
  output                    async_evt_ovl_o,
  output                    rx_buffer_ovl_o,
  output                    rx_desc_ovl_o,
  output                    transfer_err_o,
  output                    transfer_aborted_o,

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

  import i3c_async_event_pkg::*;
  import i3c_targ_ccc_pkg::*;
  import i3c_tti_pkg::*;

  // Local parameters.
  localparam int unsigned NumTargetsW = $clog2(NumTargets);
  localparam int unsigned MaxGroupsW  = $clog2(MaxGroups);

  // Additional Target info required by the Target Core logic; this is required for CCC handling,
  // but not needed by the transceiver logic.
  i3c_targ_info_t targ_info[NumTargets];
  always_comb begin : drv_targ_info
    for (int unsigned t = 0; t < NumTargets; t++) begin
      targ_info[t] = '0;
      targ_info[t].dcr =  reg2hw_i.targ_char[t].dcr.q;
      targ_info[t].bcr =  reg2hw_i.targ_char[t].bcr.q;
      targ_info[t].pid = {reg2hw_i.targ_char[t].pid_hi.q, reg2hw_i.targ_pid_lo[t].q};
    end
    // The Standby Controller configuration may override Target 0 register configuration.
    if (stby_cr_enabled_i) begin
      targ_info[0].dcr = stby_cr_dcr_i;
      targ_info[0].bcr = stby_cr_bcr_i;
      targ_info[0].pid = stby_cr_pid_i;
    end
  end

  // Format the supplied unit data ready for HDR-DDR transmission; this is used to populate
  // both `i3c_targ_trx_txd_t` (Private Read transfers) and `i3c_targ_trx_txc_t` (Direct Read CCCs).
  task automatic fmt_data_out(output logic [8:0] data_nq, output logic [8:0] data_pq,
                              output logic [1:0] rlast, input logic [15:0] unit_data,
                              input logic rdata_first, input logic [1:0] unit_rlast);
    data_nq[8] = 1'b1;
    data_pq[8] = !rdata_first;
    for (int unsigned b = 4; b < 8; b++) begin
      data_nq[b] = unit_data[2*b-7];
      data_pq[b] = unit_data[2*b-8];
    end
    // Ensure that the LS byte of a 16-bit HDR-DDR word is zero if the MS byte is the last byte.
    for (int unsigned b = 0; b < 4; b++) begin
      data_nq[b] = unit_data[2*b+9] & ~unit_rlast[0];
      data_pq[b] = unit_data[2*b+8] & ~unit_rlast[0];
    end
    rlast = unit_rlast;
  endtask

  // Interface to Command Command Code handling.
  i3c_targ_ccc_req_t ccc_req;
  i3c_targ_ccc_rsp_t ccc_rsp;

  // Register state for CCC handling.
  logic [TargCRWidth-1:0] reg_state[TargCR_Count];

  // There is a single 'Virtual Target Detect' bit that is shared among all Virtual Targets
  // (I3C Basic 4.3.7.3.23.2); a Controller may use this to correlate the Virtual Targets.
  logic virt_targ_det;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) virt_targ_det <= 1'b0;
    // TODO: Other conditions can modify the programmed Reset Action.
    else if (rstact_de_o && rstact_d_o inside {RstAct_VirtualTargDet, RstAct_NoReset}) begin
      if (rstact_d_o == RstAct_NoReset)             virt_targ_det <= 1'b0; // Clear reset action
      else if (rstact_d_o == RstAct_VirtualTargDet) virt_targ_det <= 1'b1; // Set reset action
    end
  end
  assign virt_targ_det_o = virt_targ_det;

  // Vendor Test Mode active/inactive?
  // - this state bit is the only part implemented in hardware; the provision of a random PID is the
  //   responsibility of software.
  logic vend_test_mode_q;
  logic test_mode_de;
  logic test_mode_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) vend_test_mode_q <= 1'b0;
    else if (sw_reset_i) vend_test_mode_q <= 1'b0;
    else if (test_mode_de) vend_test_mode_q <= test_mode_d;
  end
  assign vend_test_mode_o = vend_test_mode_q;  // to register interface.

  // Protocol Error state.
  logic protocol_error_q;
  logic protocol_error_de;
  logic protocol_error_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) protocol_error_q <= 1'b0;
    else if (sw_reset_i) protocol_error_q <= 1'b0;
    else if (protocol_error_de) protocol_error_q <= protocol_error_d;
  end
  assign protocol_error_o = protocol_error_q;  // to register interface.

  // TODO(#31068): Protocol errors are not yet detected/set; only the GETSTATUS-triggered clear
  // (Table 27) is connected so far (from the Target CCC handling below).
  logic protocol_error_de_ccc;
  logic protocol_error_d_ccc;
  assign protocol_error_de = protocol_error_de_ccc;
  assign protocol_error_d  = protocol_error_d_ccc;

  // Under software control, the hardware may read and drop DWORDs from any transmit buffer.
  // - IBI is source 0, so that it does not vary with the number of configured targets.
  localparam int unsigned SinkBuffers = NumTargets + 1;  // One extra for IBI, at offset 0.
  logic [SinkBuffers-1:0] sink_rready;

  // Are there any Pending Read Notifications?
  // - special descriptors are introduced into the Tx Desc queue before the Transfers themselves.
  logic [NumTargets-1:0] prn_rvalid;
  // Tx Descriptors and their validity indicators.
  logic [NumTargets-1:0] tx_desc_valid;
  i3c_tti_tx_desc_t tx_desc[NumTargets];

  // Was the arbitration request (toggle-style signalling) processed by the transceiver?
  logic prev_arb_toggle, arb_toggle_edge;
  assign arb_toggle_edge = arb_toggle_i ^ prev_arb_toggle;

  // Latched version of the IBI arbiter gnt
  logic [NumTargets+1:0] arb_gnt_q;

  // The single physical Target and FSM implement a number of Virtual Targets.
  // - each Virtual Target has its own Transmit Data Buffer and Tx Descriptor Queue in order to
  //   be ready to respond promptly to a Private Read transfer from the Active Controller.
  // - Tx Descriptor and Tx Data word are prefetched from shared storage and handled here.
  for (genvar t = 0; t < NumTargets; t++) begin : gen_splitters
    logic        tx_desc_consumed;
    logic  [3:0] tx_start_thld;
    logic        tx_thld_reached;
    logic        tx_desc_len_reached;
    logic        tx_suspended;
    logic [15:0] tx_data_len;
    logic        tx_active;
    logic        tx_rvalid;
    logic        tx_start;
    logic        unit_valid;
    logic        unit_ready;
    logic [15:0] unit_data;

    // Reinterpret as a descriptor.
    assign tx_desc[t] = i3c_tti_tx_desc_t'(tx_desc_rdata_i[t]);
    // Descriptor is valid if it is a pending read notification or contains data.
    assign tx_desc_valid[t] = |{tx_desc[t].prn.notify, tx_desc[t].tx.data_length};
    // TODO: Aborting is not yet implemented.
    assign tx_suspended = reg2hw_i.targ_pio_control.suspended.q[t];
    // TODO: Post response and/or raise error interrupt if not valid.

    // Have we enough data available to commence transmission? Fire on either
    // - At least as many DWORDs in buffer as dictated in descriptor, or
    // - At least as many DWORDs in buffer as dictated by tx threshold (threshold is power-of-two)
    assign tx_start_thld       = reg2hw_i.targ_tx_thld_ctrl[t].tx_start_thld.q;
    assign tx_desc_len_reached = {buf_rused_i[t], 2'b00} >= tx_desc[t].tx.data_length;
    assign tx_thld_reached     = |(buf_rused_i[t][FIFODepthW:1] >> tx_start_thld);

    assign tx_start = (tx_desc_len_reached || tx_thld_reached) && !tx_suspended;

    // Is this Tx Descriptor describing a Read Transfer?
    assign tx_rvalid = tx_desc_rvalid_i[t] & !tx_desc[t].tx.notify;
    // Maybe it's a Pending Read Notification?
    assign prn_rvalid[t] = tx_desc_rvalid_i[t] & tx_desc[t].tx.notify;

    // Decompose the message buffer data into individual data units for transmission.
    // - note that we don't know whether the Private Read data will be collected in SDR or
    //   HDR-DDR mode, so we must present 16 bits and then consume the data in response to
    //   the bus mode indicated at the moment of transmission.
    i3c_dword_splitter u_dword_split (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),

      .clr_i     (tx_desc_consumed),

      // Input DWORDs.
      // - full DWORDs are supplied and `clr_i` is then asserted at the end of the transfer;
      //   this also supports easier recovery.
      .valid_i   (buf_rvalid_i[t] & buf_rready_o[t]),
      .data_i    (buf_rdata_i[t]),

      // Output data units.
      .valid_o   (unit_valid),
      .ready_i   (unit_ready),
      .ddr_mode_i(ddr_mode_i),
      .data_o    (unit_data)
    );

    // Collect DWORD from buffer.
    assign buf_rready_o[t] = &{enable_i, tx_rvalid, !unit_valid, tx_start | tx_active} |
                              (enable_i & sink_rready[t + 1]);

    // Since we are driving data into an irregularly-clocked domain, new data is supplied by
    // inverting a toggle signal and waiting for it to be echoed back to us.
    logic prev_txd_toggle;
    assign txd_toggle_o[t] = (unit_valid & |tx_data_len) ^ prev_txd_toggle;

    logic rdata_first;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        prev_txd_toggle <= 1'b0;
        rdata_first <= 1'b1;
      end else if (unit_valid & unit_ready) begin
        prev_txd_toggle <= !prev_txd_toggle;
        rdata_first <= 1'b0;
      end else if (&{tx_rvalid, tx_desc_valid[t], tx_start, !tx_active}) begin
        rdata_first <= 1'b1;
      end
    end
    assign unit_ready = txd_toggle_i[t] ^ prev_txd_toggle;

    // We do not initially know the reception mode (SDR or HDR-DDR) so must provide two 'last byte'
    // indications and leave the transceiver logic to decide whether this concludes the transfer.
    wire  [1:0] unit_rlast = {tx_data_len <= 16'h2, tx_data_len < 16'h2};
    wire [15:0] unit_bytes = {14'b0, ddr_mode_i, !ddr_mode_i};
    wire rlast = unit_rlast[0] | (ddr_mode_i & unit_rlast[1]);   //(tx_data_len <= unit_bytes);
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        tx_active   <= 1'b0;
        tx_data_len <= '0;
      end else if (&{tx_rvalid, tx_desc_valid[t], tx_start, !tx_active}) begin
        tx_active   <= 1'b1;
        tx_data_len <= tx_desc[t].tx.data_length;
      end else if (tx_active & unit_ready) begin
        // This ensures that `tx_data_len` returns to zero, even if the requested data length is not
        // a multiple of the transfer unit.
        tx_data_len <= {16{!rlast}} & (tx_data_len - unit_bytes);
        // TODO: I guess we don't have a verdict until there's a reply from the transceiver,
        // so keep tx_active asserted?
        tx_active   <= !rlast;
      end
    end

    // Data for Read Transfers is supplied in anticipation of HDR-DDR collection, and the
    // transceiver reformats it for SDR collection if required.
    always_comb begin : drv_txd_data
      txd_data_o[t] = '0;
      fmt_data_out(txd_data_o[t].rdata_nq, txd_data_o[t].rdata_pq, txd_data_o[t].rlast,
                   unit_data, rdata_first, unit_rlast);
    end

    // Consume the descriptor only when all data has been presented for transmission and it is no
    // longer required, or if it's invalid.
    // TODO: We must receive some kind of verdict from the transceiver, not just wait until accepted
    assign tx_desc_consumed = tx_rvalid & (tx_suspended | &{tx_active, rlast, unit_ready});
    assign tx_desc_rready_o[t] = tx_desc_consumed | (arb_toggle_edge & arb_gnt_q[t+2]);

    // Suspend transmissions from this Virtual Target in the event of an error.
    assign suspend_tx_o[t] = tx_rvalid & !tx_desc_valid[t];
    // Clear the 'Abort' status when resuming.
    assign abort_clr_o[t]  = reg2hw_i.targ_pio_control.suspended.qe &
                             reg2hw_i.targ_pio_control.suspended.q[t];
  end

  // Similarly, we supply data for Direct GET CCCs using another inverting toggle.
  logic prev_txc_toggle;
  assign txc_toggle_o = ccc_rsp.req_cvalid ^ prev_txc_toggle;

  // We want to supply the next data as soon as possible.
  wire ccc_unit_ready = txc_toggle_i ^ prev_txc_toggle;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) prev_txc_toggle <= 1'b0;
    else if (ccc_rsp.req_cvalid & ccc_unit_ready) prev_txc_toggle <= !prev_txc_toggle;
  end

  // Direct Read CCC data for all Targets.
  always_comb begin : drv_txc_data
    txc_data_o = '0;
    for (int unsigned t = 0; t < NumTargets; t++) begin
      // TODO: rdata_first is hardcoded to 1'b0, which fails DDR CCC reads
      fmt_data_out(txc_data_o.rdata_nq[t], txc_data_o.rdata_pq[t], txc_data_o.rlast[t],
                   {8'b0, ccc_rsp.req_cdata[t]}, 1'b0, {1'b0, ccc_rsp.req_clast});
    end
  end

  // A very simple FSM mediates the handling of Common Command Codes (CCCs).
  typedef enum logic [2:0] {
    Inactive,
    // TODO: Idle may imply that the VT has become enabled and shall respond to queues?
    Idle,

    PrivXfer,
    // PrivRead,
    // PrivWrite,

    // --- IBI delivery ---

    // --- CCC handling ---
    CCC,
    CCC_Tx,
    CCC_P  // stoP
  } state_e;

  // Current and next states.
  state_e state_q, state_d;
  // Index for CCC transmission; we must count the bytes here, whereas for reception the transceiver
  // logic does that for us.
  logic [3:0] ccc_txd_idx;

  wire ccc_active  = state_q inside {CCC, CCC_Tx, CCC_P};
  wire ccc_enabled = enable_i & ccc_active;


  logic ccc_rready, prv_rready;

  // Data received from the transceiver logic may be destined for either the Rx buffer or the
  // CCC handling.
  wire ccc_rvalid = trx_rvalid_i & |{// Just starting CCC handling.
                                     state_q == Inactive && trx_rxd_i.ccc_state == CCC_Setup,
                                     // CCC handling is ongoing.
                                     ccc_active};
  wire prv_rvalid = trx_rvalid_i & !ccc_rvalid;

  // Accept responses immediately.
  // TODO: we should still be detecting and reporting any data loss here, e.g. unresponsive
  // Rx data buffer. Buffer may be full, in particular.
  assign prv_rready = prv_rvalid;

  // TODO: May need to handle buffer full conditions here; async event queue, perhaps rx buffer
  // for some very specific CCCs with large payloads such as DEFTGTS?
  assign ccc_rready = ccc_rvalid;

  assign trx_rready_o = ccc_rready | prv_rready;

  // Entering CCC Tx in response to a Direct Read request?
  logic ccc_tx_start;

  // Transition to the next state?
  // Note: this is overkill at present since the _trx logic is tracking CCC segments and counting
  // the bytes within each; it just passes this information to us.
  logic proceed;
  always_comb begin : drv_proceed
    proceed = 1'b0;
    case (state_q)
      Inactive: proceed = trx_rvalid_i;
      PrivXfer: proceed = stop_det_i;  // TODO: Want to define here what happens w.r.t. Sr?
                                       //       Important e.g., for the legal combination of
                                       //       S | Addr+W | RegAddr | Sr | Addr+R | ReadData | P
      CCC:      proceed = ccc_tx_start | stop_det_i;  // TODO: Shall likely want error-handling.
      CCC_Tx:   proceed = ccc_unit_ready | stop_det_i;  // TODO: Shall likely want error-handling.
      // All other states are immediately responsive.
      default:  proceed = 1'b1;
    endcase
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      Inactive: begin
          case (trx_rxd_i.ccc_state)
            CCC_Setup: state_d = CCC;
            default:   state_d = PrivXfer;
          endcase
        end
      PrivXfer: state_d = Inactive;
      CCC:      state_d = stop_det_i ? CCC_P : CCC_Tx;
      // TODO: ENTDAA perhaps requires a transmission back to CCC?
      CCC_Tx:   state_d = stop_det_i ? CCC_P : (ccc_rsp.req_clast ? CCC : CCC_Tx);
      CCC_P:    state_d = Inactive;
      default:  state_d = Inactive;
    endcase
  end

  // Target core state machine.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= Inactive;
      ccc_txd_idx <= 'b0;
    end else if (sw_reset_i) begin
      state_q <= Inactive;
      ccc_txd_idx <= 'b0;
    end else if (proceed) begin  // The progress of the state machine is conditional.
      state_q <= state_d;
      // We must track the current position within transmitted data, for the CCC decoding to use.
      ccc_txd_idx <= ccc_tx_start ? 'b1 : (ccc_txd_idx + ccc_unit_ready);
    end
  end

  // We must start prefetching the read data before the address has been matched.
  // TODO: Once basically working, I think we need to re-express this - perhaps with the cooperation
  // of the _trx logic - as additional states to indicate whether we're in a read-prefetching
  // segment, a write segment or a setup segment.
  wire ccc_rd_prefetch = direct_get(reg_state[TargCR_CCC]) &&
                         (trx_rxd_i.ccc_state inside {CCC_SegAddr, CCC_SegData});

  assign ccc_tx_start = &{trx_rvalid_i, trx_rxd_i.sr, ccc_rd_prefetch};

  // Construction of request to the CCC handling.
  always_comb begin : drv_ccc_req
    ccc_req = '0;
    // TODO: We could action the P a cycle earlier and drop the additional states?
    // Is there potential for the P to leapfrog the final byte, in which case we
    // perhaps use _P to retain that information and treat `trx_rvalid_i` the same in
    // each state?
    case (state_q)
      Inactive: ccc_req.en = trx_rvalid_i & (trx_rxd_i.ccc_state == CCC_Setup);
      CCC:      ccc_req.en = trx_rvalid_i;
      CCC_Tx:   ccc_req.en = ccc_unit_ready;
      CCC_P:    ccc_req.en = 1'b1;
      default:  ccc_req.en = 1'b0;
    endcase
    // The transceiver logic has already done the CCC phase and index tracking for us.
    // TODO: Presently the Sr and P processing relies on - for example - the idx being stable,
    //       we may need to capture it, to be certain of the segment/phase length.
    ccc_req.idx = ccc_rd_prefetch + (trx_rxd_i.ccc_state == CCC_SegData) + trx_rxd_i.ccc_idx[3:0];
    case (state_q)
      Inactive,
      CCC: begin
        if (trx_rxd_i.sr) begin
          if (ccc_rd_prefetch) begin
            // We must start prefetching the read data before the address has been matched.
            ccc_req.rsn = TargCRsn_TxD;
            ccc_req.idx = 'b0;
          end else ccc_req.rsn = TargCRsn_Sr;
        end else ccc_req.rsn = trx_rxd_i.rnw  ? TargCRsn_TxD : TargCRsn_RxD;
      end
      CCC_Tx: begin
        ccc_req.rsn = TargCRsn_TxD;
        ccc_req.idx = ccc_txd_idx;
      end
      CCC_P: ccc_req.rsn = TargCRsn_P;
      default: begin end
    endcase
    ccc_req.sr    = (trx_rxd_i.ccc_state != CCC_Setup);
    ccc_req.rnw   = trx_rxd_i.rnw;
    ccc_req.re    = (state_q == CCC);
    ccc_req.rdata = trx_rxd_i.wdata[7:0];
    // Additional information for the addressing phase (following Sr); the transceiver logic has
    // already done the address matching for us.
    ccc_req.targ_id  = trx_rxd_i.targ_id;
    ccc_req.is_group = trx_rxd_i.is_group;
  end

  // Diagnostic visibility.
  assign fsm_state_o = 8'(state_q);

  // Updating of CCC register state.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // Register state is zero-initialized but nothing shall depend upon it; no sw reset required.
      for (int unsigned r = 0; r < TargCR_Count; r++) reg_state[r] <= '0;
    end else if (ccc_rsp.reg_we) begin
      // Update the selected register.
      reg_state[ccc_rsp.reg_widx] <= ccc_rsp.reg_wdata;
      // When capturing the CCC or DEFB we also need to modify other state; since this is true for
      // all Common Command Codes we opt to do it here.
      case (ccc_rsp.reg_widx)
        TargCR_CCC: begin
          // Set the initial set of Targets involved in this CCC.
          // - note that a Broadcast CCC affects only the responsive targets, and the transceiver
          //   has already determined this for us.
          reg_state[TargCR_Targets] <= broadcast_ccc(ccc_rsp.reg_wdata) ? trx_rxd_i.targ_set : 'b0;
          // Declare 'no DEFB' until it is received.
          reg_state[TargCR_Status][TargStat_HasDEFB] <= 1'b0;
        end
        TargCR_DEFB: reg_state[TargCR_Status][TargStat_HasDEFB] <= 1'b1;
        // Some CCCs need to know whether the addresses is a Group or an individual Target.
        TargCR_Targets: reg_state[TargCR_Status][TargStat_IsGroup] <= trx_rxd_i.is_group;
        default: begin end
      endcase
    end
  end

  // Control signals from CCC handling.
  logic                  grp_set;
  logic                  grp_rst;
  // SETGRPA and RSTGRPA may subscribe/unsubscribe multiple targets.
  logic [NumTargets-1:0] grp_targets;
  // RSTGRPA may affect all groups or rather than just a single Group address.
  logic                  grp_all;
  logic            [6:0] grp_addr;

  // Target-side Common Command Code handling.
  i3c_target_ccc #(
    .NumTargets(NumTargets)
  ) u_target_ccc (
    // CCC handling enabled and active?
    .enable_i(ccc_enabled),

    // Configuration.
    .reg2hw_i(reg2hw_i),

    // Register state, including the CCC itself.
    .r_i(reg_state),

    // Requests from the Target FSM.
    .ccc_req_i(ccc_req),

    // Responses to the Target FSM.
    .ccc_rsp_o(ccc_rsp),

    // Writes to register state.
    .dynaddr_de_o       (dynaddr_de_o),
    .dynaddr_valid_d_o  (dynaddr_valid_d_o),
    .dynaddr_d_o        (dynaddr_d_o),
    .mwl_de_o           (mwl_de_o),
    .mrl_de_o           (mrl_de_o),
    .ibi_de_o           (ibi_de_o),
    .mwl_d_o            (mwl_d_o),
    .mrl_d_o            (mrl_d_o),
    .ibi_d_o            (ibi_d_o),
    .endis_event_o      (endis_event_o),
    .rstact_de_o        (rstact_de_o),
    .rstact_d_o         (rstact_d_o),
    .grp_set_o          (grp_set),
    .grp_rst_o          (grp_rst),
    .grp_all_o          (grp_all),
    .grp_addr_o         (grp_addr),
    .grp_targets_o      (grp_targets),
    .act_state_de_o     (act_state_de_o),
    .act_state_d_o      (act_state_d_o),
    .endxfer_cand_de_o  (endxfer_cand_de_o),
    .endxfer_cand_d_o   (endxfer_cand_d_o),
    .endxfer_de_o       (endxfer_de_o),
    .endxfer_d_o        (endxfer_d_o),
    .test_mode_de_o     (test_mode_de),
    .test_mode_d_o      (test_mode_d),
    .protocol_error_de_o(protocol_error_de_ccc),
    .protocol_error_d_o (protocol_error_d_ccc)
  );

  // Transmission outcome; for completion signaling and error reporting.
  logic [NumTargetsW-1:0] tx_targ_id;
  assign tx_targ_id = '0;  // TODO: FSM Tracks target.
  i3c_tti_tx_desc_t tx_desc_curr;
  assign tx_desc_curr = i3c_tti_tx_desc_t'(tx_desc_rdata_i[tx_targ_id]);
  i3c_tti_ibi_status_t ibi_desc;
  assign ibi_desc = i3c_tti_ibi_status_t'(ibi_desc_rdata_i);

  // TODO: Status outcomes.
  i3c_err_status_e txd_status, ibi_status;
  assign txd_status = ErrStatus_OK;
  assign ibi_status = ErrStatus_OK;

  // TODO: Remaining byte count; this is multiplexed from the various transmission paths.
  logic [15:0] tx_bytes_left;
  assign tx_bytes_left = 16'hffff;

  // Decide which Target, if any, shall participate next in Dynamic Address Assignment.
  logic [NumTargets-1:0] daa_contenders;
  for (genvar t = 0; t < NumTargets; t++) begin : gen_daa_contenders
    assign daa_contenders[t] = reg2hw_i.targ_enable[t].q &&
                              !reg2hw_i.targ_addr[t].dynamic_addr_valid.q;
  end
  logic                   daa_targ_valid; // TODO: Currently unused.
  logic [NumTargetsW-1:0] daa_targ_id;    // TODO: Currently unused.

  prim_arbiter_fixed #(.N(NumTargets), .DW(1), .EnDataPort(0)) u_daa_arb (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .req_i  (daa_contenders),
    .data_i ('{default:'0}),
    .gnt_o  (),  // Not used
    .idx_o  (daa_targ_id),
    .valid_o(daa_targ_valid),
    .data_o (),  // Not used
    .ready_i(1'b1)
  );

  // Widen the write mask to bit level, so that unused bytes will be written as zeros.
  // - this may be helpful to software, although it shouldn't be using those bytes, but it's mainly
  //   useful in modeling the hardware for verification purposes.
  logic [DataWidth/8-1:0] buf_wmask;
  logic   [DataWidth-1:0] buf_wmask_full;
  for (genvar b = 0; b < DataWidth/8; b++) begin : gen_wmask_full
    assign buf_wmask_full[8*b +: 8] = {8{buf_wmask[b]}};
  end

  // Note also that i3c_dword_collector does not store the DWORD presently, so we do that here.
  // TODO: Adjust the i3c_dword_collector for a better fit.
  logic                 buf_wvalid;
  logic                 buf_wvalid_q;
  logic [DataWidth-1:0] buf_wdata;
  logic [DataWidth-1:0] buf_wdata_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      buf_wvalid_q <= 1'b0;
      buf_wdata_q  <= '0;
    end else if (sw_reset_i) begin
      buf_wvalid_q <= 1'b0;
    end else begin
      if (buf_wvalid | buf_wready_i) buf_wvalid_q <= buf_wvalid;
      if (buf_wvalid) buf_wdata_q <= buf_wmask_full & buf_wdata;
    end
  end

  assign buf_wvalid_o = buf_wvalid_q;
  assign buf_wdata_o  = buf_wdata_q;

  // Broadcast CCCs received in Standby Controller Mode.
  // - these must be posted into HCI IBI Queue (HCI 8.6.7)
  assign stby_bcst_wvalid_o = buf_wvalid_q; // TODO: This must be further qualified.
  assign stby_bcst_wdata_o  = buf_wdata_q;

  // Excess Private Write Data from the Active Controller must just be dropped; there is no
  // accept/reject signaling mechanism on I3C SDR.
  // TODO: Provide up-front indication to the transceiver of max DDR length transmission?
  logic rx_drop, rx_flush;

  wire dtype_crc  = (trx_rxd_i.dtype == I3CDType_CRCWord);
  wire dtype_data = (trx_rxd_i.dtype inside {I3CDType_DataWord, I3CDType_SDRBytes});
  // TODO: trx_rready_o is currently OR-wired to prv_rvalid
  wire rx_data_beat = prv_rvalid & dtype_data & trx_rready_o;
  wire rx_accepted  = rx_data_beat & !rx_drop;

  // Flooding error has actually occurred.
  logic rx_flood_q;
  wire rx_flood = rx_data_beat & rx_drop;

  // Construction of TTI Rx Descriptors.
  // - an initial descriptor informs the driver of the addressing information, setting `start.`
  // - zero or more intermediate descriptors are then written, describing the transfer as segments.
  // - the final descriptor for the transfer must include `status` and set `complete.`
  //
  // TODO: The TTI was extended _after_ this logic was built. It was realized that support for
  // transfers longer than the allocated space will be required, in which case we must construct
  // multiple connected descriptors, see `i3c_tti_pkg`
  i3c_tti_rx_desc_t rx_desc_q, rx_desc_d;
  logic [13:0] next_data_len;
  logic [13:0] rx_data_len;
  logic rx_desc_wvalid, rx_desc_accepted;
  logic rx_desc_stall, rx_active_q;
  always_comb begin
    rx_desc_d = '0;
    rx_desc_d.start       = 1'b1;
    rx_desc_d.complete    = 1'b1;
    // Only the loss of received _data_ is reported here; an inability to write the descriptor
    // itself is reported via `rx_desc_ovl_o` and must not be attributed to this transfer, which
    // is a later one than the transfer whose descriptor was lost.
    rx_desc_d.status      = rx_flood_q ? TTIRxStatus_RxOverflow : trx_rxd_i.status;
    rx_desc_d.targets     = (trx_rxd_i.targ_id < NumTargets) ? NumTargets'('b1 << trx_rxd_i.targ_id)
                                                             : NumTargets'(trx_rxd_i.targ_set);
    rx_desc_d.address     = trx_rxd_i.addr;
    rx_desc_d.is_group    = trx_rxd_i.is_group;
    rx_desc_d.data_length = rx_data_len;
  end

  // The descriptor queue cannot presently accept the descriptor that is already awaiting writing.
  assign rx_desc_stall = rx_desc_wvalid & !rx_desc_wready_i;

  // Will we have to drop any more read data at this point?
  // - note that `rx_flood_q` makes any drop persistent for the remainder of the transfer,
  //   whatever its cause, so that a transfer is never captured only in part.
  // TODO: rx_data_len will always have even values if trx_rxd_i.dtype != I3CDType_SDRBytes, so
  //       &rx_data_len will never fire in the DDR case: We therefore need to check for
  //       &rx_data_len[13:1] in DDR mode instead.
  assign rx_drop = |{buf_wvalid_q & !buf_wready_i, // Transient: Data path full.
                     rx_desc_stall,                // Transient: Descriptor path full.
                     rx_flood_q, &rx_data_len};    // Persistent until end of the transfer.

  // TODO: For SDR, flush is currently only triggered on a per-frame basis on a P. This means that
  //       with frames which contain segments to multiple targets (separated via Sr), all traffic
  //       ends up in the rx buffer with the address in the descriptor set to the target that the
  //       first block of data was meant for.
  assign rx_flush = (stop_det_i & rx_active_q) ||  // SDR
                    (prv_rvalid & dtype_crc);      // HDR-DDR

  // Descriptor written to buffer
  assign rx_desc_accepted = rx_desc_wvalid & rx_desc_wready_i;

  // TODO: tx downcounting and rx upcounting could probably be combined if careful, certainly
  // the adder and perhaps the storage too? We'd have to accommodate the prefetching, probably by
  // keeping the descriptor available, but we may want that for 'wroc' et al anyway.
  assign next_data_len = rx_data_len + ((trx_rxd_i.dtype == I3CDType_SDRBytes) ? 14'h1 : 14'h2);

  // Track the number of bytes of received data and then emit the TTI Rx Descriptor.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rx_desc_wvalid  <= 1'b0;
      rx_data_len     <= '0;
      rx_desc_q       <= '0;
      rx_flood_q      <= 1'b0;
      rx_active_q     <= 1'b0;
    end else if (sw_reset_i) begin
      rx_desc_wvalid  <= 1'b0;
      rx_data_len     <= '0;
      rx_desc_q       <= '0;
      rx_flood_q      <= 1'b0;
      rx_active_q     <= 1'b0;
    end else if (enable_i) begin
      // Update the count of received bytes.
      if (rx_flush) begin
        rx_data_len <= '0;
      end else if (rx_accepted) begin
        rx_data_len <= next_data_len;
      end
      // Writing of the Rx Descriptor when the transfer outcome is known.
      // Don't write when the previous descriptor hasn't been accepted yet.
      if (rx_flush && (!rx_desc_wvalid || rx_desc_wready_i)) begin
        rx_desc_wvalid  <= 1'b1;
        rx_desc_q       <= rx_desc_d;
      end else if (rx_desc_accepted) begin
        // Rx Descriptor write accepted.
        rx_desc_wvalid  <= 1'b0;
      end
      // Remember that flooding occurred.
      rx_flood_q  <= rx_flood | (rx_flood_q & !rx_flush);
      // Remember that data was received, whether or not it had to be dropped; this guarantees
      // that every transfer terminates and thus that `rx_flood_q` is always cleared.
      rx_active_q <= rx_data_beat | (rx_active_q & !rx_flush);
    end
  end

  assign rx_desc_wvalid_o = rx_desc_wvalid;
  assign rx_desc_wdata_o  = rx_desc_q;

  // Raise an error interrupt when flooding first occurs.
  assign rx_buffer_ovl_o = enable_i & rx_flood & !rx_flood_q;

  // Report the loss of an Rx Descriptor; the transfer had completed but the descriptor describing
  // it could not be written because the previous descriptor was still awaiting acceptance.
  // Note that the associated data has already been dropped, since `rx_desc_stall` is a term into
  // `rx_drop`. This is necessary in order for the descriptor and data streams to remain in step.
  assign rx_desc_ovl_o = enable_i & rx_flush & rx_desc_stall;

  // Collect received bytes to form complete DWORDs for buffer writing.
  i3c_dword_collector u_dword_collect (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),

    .clr_i     (sw_reset_i),

    // Input SDR bytes/HDR-DDR Data Words.
    .valid_i   (rx_accepted),
    .flush_i   (rx_flush),
    .ddr_mode_i(ddr_mode_i),
    .data_i    (trx_rxd_i.wdata),

    // Output DWORDs.
    .valid_o   (buf_wvalid),
    .mask_o    (buf_wmask),
    .data_o    (buf_wdata)
  );

  /* In-Band Interrupts.
     This logic also handles the following asynchronous requests of the current Active Controller:
     - Controller-Role Requests.
     - Hot-Join Requests.
     - Pending Read Data notifications.
  */

  // Remove the IBI Status Descriptor from the FIFO once we've been granted the bus.
  assign ibi_desc_rready_o = enable_i & arb_toggle_edge & arb_gnt_q[0];
  // TODO: Drop the IBI data immediately for now...
  assign ibi_rready_o = enable_i & ((ibi_desc_rvalid_i & ibi_rvalid_i) | sink_rready[0]);

  wire         ibi_desc_consumed = 1'b0;
  logic [15:0] ibi_unit_data; // TODO: Currently unused.
  logic        ibi_unit_valid;
  logic        ibi_unit_ready;

  // Decompose the DWORDs from the IBI Data Buffer into bytes (IBIs are SDR only).
  i3c_dword_splitter u_ibi_split (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),

    .clr_i     (ibi_desc_consumed),

    // Input DWORDs.
    // - full DWORDs are supplied and `clr_i` is then asserted at the end of the transfer;
    //   this also supports easier recovery.
    .valid_i   (ibi_rvalid_i & ibi_rready_o),
    .data_i    (ibi_rdata_i),

    // Output data units.
    .valid_o   (ibi_unit_valid),
    .ready_i   (ibi_unit_ready),
    .ddr_mode_i(1'b0),  // IBIs are always sent in SDR mode.
    .data_o    (ibi_unit_data)
  );

  // TODO: Splitter it not used because IBI transmission is incomplete.
  assign ibi_unit_ready = ibi_unit_valid;

  // Is the first Target operating as a Standby Controller that requires attention?
  // TODO: We at least need an interface for specifying that the first VT (not StbyCr) wants HJ.
  wire hotjoin_stby_ctrl = (stby_cr_enable_init_i == StbyCrEn_SCMHotJoin);
  wire cr_req_stby_ctrl  = stby_cr_cr_req_send_i;
  // We need to support Hot-Join when not in Standby Controller mode, but not CRR.
  wire ibi_stby_ctrl = (stby_cr_enabled_i & cr_req_stby_ctrl) | hotjoin_stby_ctrl;

  // Reinterpret IBI Status Queue data as a descriptor.
  i3c_tti_ibi_status_t ibi_stat_desc;
  logic ibi_dispatch, ibi_got_mdb, ibi_stat_desc_valid;
  assign ibi_stat_desc = i3c_tti_ibi_status_t'(ibi_desc_rdata_i);
  assign ibi_stat_desc_valid = (ibi_stat_desc.targ_id < NumTargets) &
                               |ibi_stat_desc.data_length;  // Enforce the presence of the MDB.

  assign ibi_got_mdb  = ibi_rvalid_i;
  assign ibi_dispatch = ibi_desc_rvalid_i & ibi_stat_desc_valid & ibi_got_mdb;

  // IBI Transmission suspended.
  assign ibi_suspend_tx_o = ibi_desc_rvalid_i & !ibi_stat_desc_valid;
  // Clear the 'Abort' status when resuming.
  assign ibi_abort_clr_o  = reg2hw_i.targ_pio_control.ibi_suspended.qe &
                            reg2hw_i.targ_pio_control.ibi_suspended.q;

  // Return the 9 SDR bits to be transmitted for the Mandatory Data byte of an In-Band Interrupt
  // request; the final bit indicates whether there is more data to follow.
  function automatic logic [8:0] mand_data_nq(logic [7:0] rdata, logic [7:0] len);
    return {rdata[7:0], |len};
  endfunction

  // Arbitrate amongst IBI, HJ/CRR and any Pending Read Notifications.
  localparam int unsigned IBIArbDataW = $bits(i3c_targ_trx_arb_t);
  i3c_targ_trx_arb_t ibi_arb_in[NumTargets + 2];
  logic  [NumTargets+1:0] ibi_arb_req, ibi_arb_gnt;
  logic [NumTargetsW-1:0] ibi_targ_id_clamp;
  always_comb begin
    for (int unsigned c = 0; c < NumTargets + 2; c++) ibi_arb_in[c] = '0;
    ibi_targ_id_clamp = ibi_stat_desc.targ_id < NumTargets ? NumTargetsW'(ibi_stat_desc.targ_id)
                                                           : '0;
    // The highest-priority contender is any In-Band Interrupt from the queue.
    ibi_arb_req[0] = ibi_dispatch;
    ibi_arb_in[0].targ_id  = ibi_stat_desc.targ_id;
    ibi_arb_in[0].addr     = targ_dev_i[ibi_targ_id_clamp].addr;
    ibi_arb_in[0].ibi      = 1'b1;
    ibi_arb_in[0].rdata_nq = mand_data_nq(ibi_stat_desc.mdb, ibi_stat_desc.data_length);
    // Hot-Join Request/Controller Role Request; single contender.
    ibi_arb_req[1] = ibi_stby_ctrl;
    ibi_arb_in[1].addr = hotjoin_stby_ctrl ? 7'h02 : targ_dev_i[0].addr;
    // This is followed by any Pending Read Notifications from the Virtual Targets.
    for (int unsigned t = 0; t < NumTargets; t++) begin
      ibi_arb_req[t + 2] = prn_rvalid[t] & tx_desc_valid[t];
      ibi_arb_in[t + 2].targ_id  = TargIDW'(t);
      ibi_arb_in[t + 2].addr     = targ_dev_i[t].addr;
      ibi_arb_in[t + 2].ibi      = 1'b1;
      ibi_arb_in[t + 2].rdata_nq = mand_data_nq({3'b101, tx_desc[t].prn.lsbs},  // MDB.
                                                {6'b0,   tx_desc[t].prn.len});  // More bytes?
    end
  end

  // IBI, CRR/HJ and PRN (one per target) arbitration results.
  localparam int unsigned IBIArbW = $clog2(NumTargets + 2);
  logic [IBIArbW-1:0] ibi_arb_winner; // TODO: Currently unused.
  i3c_targ_trx_arb_t ibi_arb_data;
  logic ibi_arb_valid;

  // Arbitrate amongst the Virtual Targets that currently want the attention of the Controller.
  // - Pending Read Notifications (1 per target).
  // - Hot-Join/Controller Role Request come from Standby Controller/Virtual Target 0.
  // - All In-Band Interrupts come from the associated queue.
  prim_arbiter_fixed #(
    .N(NumTargets + 2),
    .DW(IBIArbDataW),
    .EnDataPort(1)
  ) u_ibi_arb (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),

    .req_i  (ibi_arb_req),
    .data_i (ibi_arb_in),
    .gnt_o  (ibi_arb_gnt),
    .idx_o  (ibi_arb_winner),

    .valid_o(ibi_arb_valid),
    .data_o (ibi_arb_data),
    .ready_i(1'b1)
  );

  // Present the arbitration request of the winning target to the transceiver.
  // TODO: Consider whether we shall ever need to retract an arbitration request or re-prioritize.
  // The Bus Available Condition is 1us.
  always_ff @(posedge clk_i or negedge trx_rst_ni) begin
    if (!trx_rst_ni) begin
      arb_toggle_o      <= 1'b0;
      arb_data_o        <= '0;
      arb_gnt_q         <= '0;
      prev_arb_toggle   <= 1'b0;
    end else if (ibi_arb_valid & (arb_toggle_o == prev_arb_toggle)) begin
      arb_toggle_o      <= !arb_toggle_o;
      arb_data_o        <= ibi_arb_data;
      arb_gnt_q         <= ibi_arb_gnt;
    end else if (arb_toggle_edge) begin
      prev_arb_toggle   <= arb_toggle_o;
    end
  end

  // Start request to the transceiver.
  // - this is needed to raise IBI and CRR requests when there is no activity on the I3C bus.
  i3c_targ_start_req u_start_req (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),

    // Control inputs.
    .enable_i        (enable_i),
    .start_i         (ibi_dispatch),
    .reset_i         (|{sw_reset_i, stop_det_i, rep_start_det_i}),

    // IBI/CRR target address.
    .addr_i          (arb_data_o.addr[6:3]),

    // I3C clock signal from the Active Controller.
    .scl_i           (scl_i),
    // I3C data signal from the Active Controller/Targets.
    .sda_i           (sda_i),

    // Start request signaling to the transceiver.
    .sreq_sda_od_en_o(sreq_sda_od_en_o),
    .sreq_sda_o      (sreq_sda_o)
  );

  // Update the dynamic address of the Standby Controller; this is shared with the first
  // Virtual Target.
  assign stby_cr_dynaddr_de_o = dynaddr_de_o[0];
  assign stby_cr_dynaddr_d_o  = {dynaddr_valid_d_o, dynaddr_d_o[0]};

  // Notification of transmission outcomes.
  // - there can only be a single transmission outcome at a time.
  //
  // TODO: We want a response from the transceiver to indicate the outcome of the transmission.
  // TODO: We then have a question what we should do if the transfer did not complete successfully;
  // leave software to purge the Tx and Tx Desc FIFOs? Does it even have the means to do that yet?
  logic ibi_result;
  logic txd_result;
  always_comb begin
    ibi_result = 1'b0;
    txd_result = 1'b0;
  end

  logic [TTIBusEv_Count-1:0] bus_events;
  logic bus_becoming_idle;
  always_comb begin
    bus_events = '0;
    bus_events[TTIBusEv_ReadNoSCL] = 1'b0;
    bus_events[TTIBusEv_DeadBus]   = 1'b0;
    bus_events[TTIBusEv_Idle]      = bus_becoming_idle;
  end

  // Report Asynchronous Events for the start of bus condition(s).
  prim_edge_detector #(.Width(1), .ResetValue('0), .EnSync(1'b0)) u_bus_idle_edge (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .d_i              (bus_idle_i),
    .q_sync_o         (),
    .q_posedge_pulse_o(bus_becoming_idle),
    .q_negedge_pulse_o()
  );

  // Writing of Asynchronous Events descriptors into the queue.
  i3c_targ_async_events #(
    .NumTargets (NumTargets),
    .DataWidth  (DataWidth),
    .FIFODepthW (FIFODepthW)
  ) u_async_evt (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),

    // Control inputs.
    .enable_i        (enable_i),
    .sw_reset_i      (sw_reset_i | async_evt_rst_i),

    // Configuration inputs.
    .reg2hw_i        (reg2hw_i),

    // Transmission outcomes.
    .txd_result_i    (txd_result),
    .txd_status_i    (txd_status),
    .txd_targ_id_i   (tx_targ_id),
    .txd_tid_i       (tx_desc_curr.tx.tid),
    .txd_data_left_i (tx_bytes_left),

    .ibi_result_i    (ibi_result),
    .ibi_status_i    (ibi_status),
    .ibi_targ_id_i   (ibi_desc.targ_id),
    .ibi_tid_i       (ibi_desc.tid),
    .ibi_data_left_i (tx_bytes_left),

    // Suspending transmission.
    .suspend_tx_i    (suspend_tx_o),
    .ibi_suspend_tx_i(ibi_suspend_tx_o),

    // CCC traffic.
    .ccc_traffic_i   (ccc_req.en),
    // Register state
    .r_i             (reg_state),
    // Current state of CCC handling.
    .ccc_req_i       (ccc_req),

    // Bus Events.
    .bus_events_i    (bus_events),

    // Asynchronous Event Queue.
    .wvalid_o        (async_wvalid_o),
    .wdata_o         (async_wdata_o),
    .wready_i        (async_wready_i),

    // Error events.
    .overflow_o      (async_evt_ovl_o)
  );

  // Group Addressing.
  //
  // SETGRPA may need to allocate a new group index.
  // TODO: We have to communicate back to the transceiver if there is no slot available to add.
  logic                  grp_add;        // Add (write) new group?
  logic                  grp_idx_valid;  // Anything found?
  logic [MaxGroupsW-1:0] grp_idx;        // Indicates the chosen entry.
  logic                  grp_match_valid, grp_free_valid; // Address found, unused entry found
  logic [MaxGroupsW-1:0] grp_match_idx,   grp_free_idx;   // Corresponding index
  always_comb begin
    grp_match_valid = 1'b0;  grp_free_valid = 1'b0;
    grp_match_idx   = '0;    grp_free_idx   = '0;
    // Descending, so that the lowest matching/free entry wins.
    for (int grp = MaxGroups - 1; grp >= 0; grp--) begin
      if (reg2hw_i.targ_group[grp].group_addr.q == grp_addr) begin
        grp_match_valid = 1'b1;
        grp_match_idx   = MaxGroupsW'(grp);
      end else if (reg2hw_i.targ_group[grp].targets.q == '0) begin
        grp_free_valid  = 1'b1;
        grp_free_idx    = MaxGroupsW'(grp);
      end
    end
    // An entry already describing this group address always takes precedence.
    grp_add       = !grp_match_valid;
    grp_idx_valid = grp_match_valid | grp_free_valid;
    grp_idx       = grp_match_valid ? grp_match_idx : grp_free_idx;
  end

  logic [NumTargets-1:0] targs_curr;
  logic [NumTargets-1:0] targs_set;
  logic [NumTargets-1:0] targs_rst;
  assign targs_curr = {NumTargets{~grp_add}} & reg2hw_i.targ_group[grp_idx].targets.q;
  assign targs_set  = {NumTargets{ grp_set}} & grp_targets;
  assign targs_rst  = {NumTargets{ grp_rst}} & grp_targets;

  // Just leave group addresses in place when all targets become unsubscribed; we can reallocate
  // those entries above.
  for (genvar grp = 0; grp < MaxGroups; grp++) begin : gen_grp_addr
    logic [NumTargets-1:0] grp_curr;
    assign grp_curr           = grp_all ? reg2hw_i.targ_group[grp].targets.q[NumTargets-1:0]
                                        : targs_curr;
    // Are we adding a new group address?
    assign grp_addr_de_o[grp] = grp_set & grp_add & grp_idx_valid & (grp == grp_idx);
    assign grp_addr_d_o[grp]  = grp_addr;
    // Update the list of subscribed targets.
    assign grp_targ_de_o[grp] = (grp_set | grp_rst) & (grp_all | (grp_idx_valid & (grp == grp_idx)));
    assign grp_targ_d_o[grp]  = (grp_curr | targs_set) & ~targs_rst;
  end

  // Supply the 'data available' indications to the data sink.
  logic [SinkBuffers-1:0] sink_rvalid;
  for (genvar t = 0; t < NumTargets; t++) begin : gen_sink_rvalid
    assign sink_rvalid[t + 1] = buf_rvalid_i[t];
  end
  assign sink_rvalid[0] = ibi_rvalid_i;
  // Supply the 'buffer empty' indications to the data sink.
  logic [SinkBuffers-1:0] sink_empty;
  for (genvar t = 0; t < NumTargets; t++) begin : gen_sink_empty
    assign sink_empty[t + 1] = buf_rempty_i[t];
  end
  assign sink_empty[0] = ibi_rempty_i;

  // Software starts the data sink operation.
  wire sink_start = reg2hw_i.targ_sink_control.start.qe & reg2hw_i.targ_sink_control.start.q;

  // Sink for remaining DWORDs when transmission becomes suspended.
  // - this is under software control and shall be used before transmission is re-enabled.
  localparam int unsigned SinkBufW = $clog2(SinkBuffers);
  i3c_data_sink #(
    .NumBuffers (SinkBuffers)
  ) u_data_sink (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),

    // Control signals.
    .enable_i     (enable_i),
    .sw_reset_i   (sw_reset_i),

    // Start request from controlling logic.
    .start_i      (sink_start),
    // Properties of the request; static throughout operation.
    .buf_i        (reg2hw_i.targ_sink_control.buffer.q[SinkBufW-1:0]),
    .dwords_left_i(reg2hw_i.targ_sink_control.length.q[BufAddrW:0]),

    // Reporting of current state.
    .dwords_left_o(sink_dwords_left_o),

    // Activity indication; remains asserted until all DWORDs consumed, or an error is encountered.
    .active_o     (sink_active_o),
    .error_o      (sink_error_o),

    // Buffer empty indicators.
    .empty_i      (sink_empty),
    // DWORD is available for consumption.
    .rvalid_i     (sink_rvalid),
    // Ready to accept DWORD.
    .rready_o     (sink_rready)
  );

  // Optional Target-side extension logic.
  // - this interface is provided for protocols that must be implemented in hardware in order to
  //   achieve the required response time.
  if (TargetExt) begin : gen_ext
    i3c_target_ext #(
      .Dummy (1)
    ) u_ext (
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),

      // Control signals.
      .enable_i     (enable_i),
      .sw_reset_i   (sw_reset_i),

      // Indicator of hardware extension presence.
      .ext_present_o(ext_present_o),
      // Extension info.
      .ext_info_qe_i(reg2hw_i.targ_status.ext_info.qe),
      .ext_info_q_i (reg2hw_i.targ_status.ext_info.q),
      .ext_info_o   (ext_info_o),

      // Register interface.
      .ext_reg2hw_i (ext_reg2hw_i),
      .ext_hw2reg_o (ext_hw2reg_o)
    );
  end else begin : gen_no_ext
    assign ext_present_o = 1'b0;
    assign ext_info_o    = 'b0;
    assign ext_hw2reg_o  = 'b0;
  end

  // TODO: Dummy drivers for now.
  assign transfer_err_o = 1'b0;
  assign transfer_aborted_o = 1'b0;

endmodule
