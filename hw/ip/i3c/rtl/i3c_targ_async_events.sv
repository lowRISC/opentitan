// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Construction and reporting of Asynchronous Events on the Target side.
//
// - CCC traffic
// - transmission outcomes
// - suspended transmission
// - bus events

module i3c_targ_async_events
  import i3c_async_event_pkg::*;
  import i3c_consts_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
  import i3c_targ_ccc_pkg::*;
  import i3c_tti_pkg::*;
#(
  parameter int unsigned NumTargets = 2,
  parameter int unsigned DataWidth  = 32,
  parameter int unsigned FIFODepthW = i3c_fifo_pkg::DepthW,

  // Derived parameters.
  localparam int unsigned Log2NT = $clog2(NumTargets)
) (
  input                       clk_i,
  input                       rst_ni,

  // Control inputs.
  input                       enable_i,
  input                       sw_reset_i,

  // Configuration inputs.
  input  i3c_reg2hw_t         reg2hw_i,

  // Transmission outcomes.
  input                       txd_result_i,
  input  i3c_err_status_e     txd_status_i,
  input          [Log2NT-1:0] txd_targ_id_i,
  input                 [3:0] txd_tid_i,
  input                [15:0] txd_data_left_i,

  input                       ibi_result_i,
  input  i3c_err_status_e     ibi_status_i,
  input          [Log2MT-1:0] ibi_targ_id_i,
  input                 [3:0] ibi_tid_i,
  input                [15:0] ibi_data_left_i,

  // Suspending transmission.
  input      [NumTargets-1:0] suspend_tx_i,
  input                       ibi_suspend_tx_i,

  // CCC traffic.
  input                       ccc_traffic_i,
  // Register state for recording CCC traffic.
  input     [TargCRWidth-1:0] r_i[TargCR_Count],
  // Current state of CCC handling.
  input  i3c_targ_ccc_req_t   ccc_req_i,

  // Bus Events.
  input  [TTIBusEv_Count-1:0] bus_events_i,

  // Asynchronous Event Queue.
  output                      wvalid_o,
  output      [DataWidth-1:0] wdata_o,
  input                       wready_i,

  // Error events.
  output                      overflow_o
);

  logic [AsyncEv_Count-1:0] evt_captured;
  logic [AsyncEv_Count-1:0] capture;

  // The Common Command Code, including Broadcast/Direct indication.
  // - this comes from a register but is always available, along with all of the other registers.
  i3c_ccc_e ccc;
  assign ccc = i3c_ccc_e'(r_i[TargCR_CCC]);

  // Generate 'new capture' strobes by qualifying the activity strobes with the current enables.
  always_comb begin
    capture = '0;

    // These strobes are not qualified by enables but rather determined by the descriptor and the
    // outcome; unsuccessful transmissions shall always be reported.
    capture[AsyncEv_NotifyTx]   = txd_result_i;
    capture[AsyncEv_NotifyIBI]  = ibi_result_i;

    capture[AsyncEv_TxSuspend]  = |suspend_tx_i     & reg2hw_i.targ_async_evt_control.tx_suspend.q;
    capture[AsyncEv_IBISuspend] = |ibi_suspend_tx_i & reg2hw_i.targ_async_evt_control.ibi_suspend.q;
    capture[AsyncEv_BusEvents]  = |bus_events_i     & reg2hw_i.targ_async_evt_control.bus_events.q;

    // The CCC handling supports filtering by CCC category, making the decision more involved.
    if (ccc_traffic_i) begin
      capture[AsyncEv_CCC] = broadcast_ccc(ccc) ? reg2hw_i.targ_async_evt_control.bcst_ccc.q    :
                               (direct_get(ccc) ? reg2hw_i.targ_async_evt_control.dir_get_ccc.q :
                                                  reg2hw_i.targ_async_evt_control.dir_set_ccc.q);
    end
  end

  // Capture CCC traffic.
  //
  // - the aim is to report CCC activity to one or more targets, so that software is notified of any
  //   resultant configuration change.
  logic [NumTargets-1:0] ccc_targets;
  logic [6:0] ccc_address;
  logic [15:0] ccc_info;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ccc_targets <= 'b0;
      ccc_address <= 'b0;
      ccc_info    <= 'b0;
    end else if (sw_reset_i) ccc_targets <= 'b0;
    else begin
      if (capture[AsyncEv_CCC] | evt_captured[AsyncEv_CCC]) begin
        ccc_targets <= capture[AsyncEv_CCC] ? r_i[TargCR_Targets] : 'b0;
      end
      ccc_address <= 'b0;
      ccc_info    <= {r_i[TargCR_Status][TargStat_HasDEFB], r_i[TargCR_DEFB], r_i[TargCR_CCC]};
    end
  end

  // Capture transmission outcomes.
  // - only a single outcome is retained because they are temporally well-separated.
  logic               txd_result_q;
  i3c_err_status_e    txd_status_q;
  logic  [Log2NT-1:0] txd_targ_id_q;
  logic         [3:0] txd_tid_q;
  logic        [15:0] txd_data_left_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      txd_result_q    <= 1'b0;
      txd_status_q    <= ErrStatus_OK;
      txd_targ_id_q   <= 'b0;
      txd_tid_q       <= 'b0;
      txd_data_left_q <= 'b0;
    end else if (sw_reset_i) begin
      txd_result_q    <= 1'b0;
    end else begin
      if (capture[AsyncEv_NotifyTx] | evt_captured[AsyncEv_NotifyTx]) begin
        txd_result_q <= (txd_result_q & !evt_captured[AsyncEv_NotifyTx]) |
                         capture[AsyncEv_NotifyTx];
      end
      // This should never matter, but prioritize the oldest outcome.
      if (capture[AsyncEv_NotifyTx] & (!txd_result_q | evt_captured[AsyncEv_NotifyTx])) begin
        txd_status_q    <= txd_status_i;
        txd_targ_id_q   <= txd_targ_id_i;
        txd_tid_q       <= txd_tid_i;
        txd_data_left_q <= txd_data_left_i;
      end
    end
  end

  // Capture IBI transmission outcomes.
  logic               ibi_result_q;
  i3c_err_status_e    ibi_status_q;
  logic  [Log2MT-1:0] ibi_targ_id_q;
  logic         [3:0] ibi_tid_q;
  logic        [15:0] ibi_data_left_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ibi_result_q    <= 1'b0;
      ibi_status_q    <= ErrStatus_OK;
      ibi_tid_q       <= 'b0;
      ibi_data_left_q <= 'b0;
    end else if (sw_reset_i) begin
      ibi_result_q    <= 1'b0;
    end else begin
      if (capture[AsyncEv_NotifyIBI] | evt_captured[AsyncEv_NotifyIBI]) begin
        ibi_result_q <= (ibi_result_q & !evt_captured[AsyncEv_NotifyIBI]) |
                         capture[AsyncEv_NotifyIBI];
      end
      // This should never matter, but prioritize the oldest outcome.
      if (capture[AsyncEv_NotifyIBI] & (!ibi_result_q | evt_captured[AsyncEv_NotifyIBI])) begin
        ibi_status_q    <= ibi_status_i;
        ibi_targ_id_q   <= ibi_targ_id_i;
        ibi_tid_q       <= ibi_tid_i;
        ibi_data_left_q <= ibi_data_left_i;
      end
    end
  end
  // Capture transmission suspensions.
  // - these may be captured incrementally until arbitration is won.
  logic [NumTargets-1:0] suspend_tx_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) suspend_tx_q <= 'b0;
    else if (sw_reset_i) suspend_tx_q <= 'b0;
    else if (capture[AsyncEv_TxSuspend] | evt_captured[AsyncEv_TxSuspend]) begin
      suspend_tx_q <= (suspend_tx_q & !evt_captured[AsyncEv_TxSuspend]) |
                      capture[AsyncEv_TxSuspend];
    end
  end

  // Capture IBI transmission suspension.
  logic ibi_suspend_tx_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) ibi_suspend_tx_q <= 1'b0;
    else if (sw_reset_i) ibi_suspend_tx_q <= 1'b0;
    else if (capture[AsyncEv_IBISuspend] | evt_captured[AsyncEv_IBISuspend]) begin
      ibi_suspend_tx_q <= (ibi_suspend_tx_q & !evt_captured[AsyncEv_IBISuspend]) |
                           capture[AsyncEv_IBISuspend];
    end
  end

  // Capture Bus Events.
  logic [TTIBusEv_Count-1:0] bus_events_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) bus_events_q <= 'b0;
    else if (sw_reset_i) bus_events_q <= 'b0;
    else if (capture[AsyncEv_BusEvents] | evt_captured[AsyncEv_BusEvents]) begin
      bus_events_q <= (evt_captured[AsyncEv_BusEvents] ? 'b0 : bus_events_q) |
                       capture[AsyncEv_BusEvents];
    end
  end

  // Events are cleared once they have been captured into the message buffer.
  logic [AsyncEv_Count-1:0] async_gnt;
  assign evt_captured = wready_i ? async_gnt : 'b0;

  // Arbitration requests.
  logic [AsyncEv_Count-1:0] async_req;
  always_comb begin
    async_req = 'b0;
    async_req[AsyncEv_CCC]        = |ccc_targets;
    async_req[AsyncEv_NotifyTx]   = txd_result_q;
    async_req[AsyncEv_NotifyIBI]  = ibi_result_q;
    async_req[AsyncEv_TxSuspend]  = |suspend_tx_q;
    async_req[AsyncEv_IBISuspend] = ibi_suspend_tx_q;
    async_req[AsyncEv_BusEvents]  = |bus_events_q;
  end

  // Categories of Asynchronous Events to be reported to software.
  i3c_tti_async_event_t async_evt[AsyncEv_Count];
  always_comb begin
    for (int unsigned et = 0; et < int'(AsyncEv_Count); et++)
      async_evt[et] = '0;

    async_evt[AsyncEv_CCC].ccc.code = AsyncEv_CCC;
    // TODO populate this structure!
    //async_evt[AsyncEv_CCC].info    = ccc_info;

    async_evt[AsyncEv_NotifyTx].txdr.code       = AsyncEv_NotifyTx;
    async_evt[AsyncEv_NotifyTx].txdr.err_status = txd_status_q;
    async_evt[AsyncEv_NotifyTx].txdr.targ_id    = Log2MT'(txd_targ_id_q);
    async_evt[AsyncEv_NotifyTx].txdr.tid        = txd_tid_q;
    async_evt[AsyncEv_NotifyTx].txdr.data_left  = txd_data_left_q;

    async_evt[AsyncEv_NotifyIBI].ibir.code       = AsyncEv_NotifyIBI;
    async_evt[AsyncEv_NotifyIBI].ibir.err_status = ibi_status_q;
    async_evt[AsyncEv_NotifyIBI].ibir.targ_id    = ibi_targ_id_q;
    async_evt[AsyncEv_NotifyIBI].ibir.tid        = ibi_tid_q;
    async_evt[AsyncEv_NotifyIBI].ibir.data_left  = ibi_data_left_q;

    async_evt[AsyncEv_TxSuspend].txds.code    = AsyncEv_TxSuspend;
    async_evt[AsyncEv_TxSuspend].txds.targets = suspend_tx_q;

    async_evt[AsyncEv_IBISuspend].ibis.code = AsyncEv_IBISuspend;

    async_evt[AsyncEv_BusEvents].bus.code = AsyncEv_BusEvents;
    async_evt[AsyncEv_BusEvents].bus.evt  = bus_events_q;
  end

  // Arbitrate amongst the Asynchronous Event types.
  prim_arbiter_fixed #(
    .N  (AsyncEv_Count),
    .DW ($bits(i3c_tti_async_event_t)),
    .EnDataPort(1)
  ) u_arb (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),

    .req_i    (async_req),
    .data_i   (async_evt),
    .gnt_o    (async_gnt),
    .idx_o    (),

    // Write access to the queue.
    .valid_o  (wvalid_o),
    .data_o   (wdata_o),
    .ready_i  (wready_i)
  );

  // Report any failure to write into the Asynchronous Event Queue in a timely fashion.
  assign overflow_o = &{async_req & ~async_gnt, wvalid_o, !wready_i};

  // TTI Async Event union size check.
  if ($bits(i3c_tti_async_event_t) != 32) $fatal(2, "i3c_tti_async_event_t has incorrect size");

endmodule
