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

  // Derived parameters.
  localparam int unsigned Log2NT = $clog2(NumTargets)
) (
  input                       clk_i,
  input                       rst_ni,

  // Control inputs.
  input                       enable_i,  // TODO: Currently unused.
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

  // CCC request and current state of CCC handling.
  input  i3c_targ_ccc_req_t   ccc_req_i,
  // Register state for recording CCC traffic.
  input     [TargCRWidth-1:0] r_i[TargCR_Count],

  // Bus Events.
  input  [TTIBusEv_Count-1:0] bus_events_i,

  // Asynchronous Event Queue.
  output                      wvalid_o,
  output      [DataWidth-1:0] wdata_o,
  input                       wready_i,

  // Report failure to inform firmware about all events.
  output                      evt_lost_o
);

  // Signals to indicate pending capture and capturing into the message buffer.
  logic [AsyncEv_Count-1:0] capture;
  logic [AsyncEv_Count-1:0] evt_captured;

  // First byte when receiving a CCC data stream is the CCC itself.
  logic ccc_byte0;
  assign ccc_byte0 = ccc_req_i.en && (ccc_req_i.rsn == TargCRsn_RxD) && (ccc_req_i.idx == 0) &&
                     !ccc_req_i.sr;


  // The Common Command Code, including Broadcast/Direct indication.
  // - this comes from a register after the first byte has been received.
  i3c_ccc_e ccc;
  assign ccc = ccc_byte0 ? i3c_ccc_e'(ccc_req_i.rdata) : i3c_ccc_e'(r_i[TargCR_CCC]);

  // Mirrors i3c_target_ccc.sv's `wr_commit`: a CCC is fully committed either at Stop, or at a
  // repeated Start that begins the next CCC/segment.
  logic ccc_commit;
  assign ccc_commit = (ccc_req_i.rsn == TargCRsn_Sr) ? ccc_req_i.sr :
                       (ccc_req_i.rsn == TargCRsn_P);

  // Generate 'new capture' strobes by qualifying the activity strobes with the current enables.
  always_comb begin
    capture = '0;

    capture[AsyncEv_NotifyTx]   = txd_result_i & reg2hw_i.targ_async_evt_control.tx_notify.q;
    capture[AsyncEv_NotifyIBI]  = ibi_result_i & reg2hw_i.targ_async_evt_control.ibi_notify.q;

    capture[AsyncEv_TxSuspend]  = |suspend_tx_i     & reg2hw_i.targ_async_evt_control.tx_suspend.q;
    capture[AsyncEv_IBISuspend] = |ibi_suspend_tx_i & reg2hw_i.targ_async_evt_control.ibi_suspend.q;
    capture[AsyncEv_BusEvents]  = |bus_events_i     & reg2hw_i.targ_async_evt_control.bus_events.q;

    // The CCC handling supports filtering by CCC category, making the decision more involved.
    // Qualify the capture signal with ccc_commit such that it (and everything derived from it)
    // reflects a fully committed CCC and no intermittent states.
    if (ccc_req_i.en) begin
      capture[AsyncEv_CCC] = ccc_commit & (
                              broadcast_ccc(ccc) ? reg2hw_i.targ_async_evt_control.bcst_ccc.q    :
                                (direct_get(ccc) ? reg2hw_i.targ_async_evt_control.dir_get_ccc.q :
                                                   reg2hw_i.targ_async_evt_control.dir_set_ccc.q));
    end
  end

  // Capture CCC traffic.
  //
  // - the aim is to report CCC activity to one or more targets, so that software is notified of any
  //   resultant configuration change.
  logic [NumTargets-1:0] ccc_targets;
  logic [6:0] ccc_address; // TODO: Currently unused

  struct packed {
    logic [7:0] ccc;
    logic [7:0] defb;
    logic       has_defb;
  } ccc_info;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ccc_targets <= '0;
      ccc_address <= '0;
      ccc_info    <= '0;
    end else if (sw_reset_i) ccc_targets <= '0;
    else begin
      // Latch ccc_targets and ccc_info together, once per qualifying CCC.
      if (capture[AsyncEv_CCC] & (!(|ccc_targets) | evt_captured[AsyncEv_CCC])) begin
        ccc_targets <= NumTargets'(r_i[TargCR_Targets]);
        ccc_address <= '0; // TODO
        ccc_info    <= '{
          ccc:      ccc,
          defb:     r_i[TargCR_DEFB],
          has_defb: r_i[TargCR_Status][TargStat_HasDEFB]
        };
      end else if (evt_captured[AsyncEv_CCC]) begin
        ccc_targets <= '0;
      end
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
      ibi_targ_id_q   <= '0;
      ibi_tid_q       <= '0;
      ibi_data_left_q <= '0;
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
    if (!rst_ni) suspend_tx_q <= '0;
    else if (sw_reset_i) suspend_tx_q <= '0;
    else if (capture[AsyncEv_TxSuspend] | evt_captured[AsyncEv_TxSuspend]) begin
      suspend_tx_q <= (evt_captured[AsyncEv_TxSuspend] ? '0 : suspend_tx_q) |
                      (capture[AsyncEv_TxSuspend] ? suspend_tx_i : '0);
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
    if (!rst_ni) bus_events_q <= '0;
    else if (sw_reset_i) bus_events_q <= '0;
    else if (capture[AsyncEv_BusEvents] | evt_captured[AsyncEv_BusEvents]) begin
      bus_events_q <= (evt_captured[AsyncEv_BusEvents] ? '0 : bus_events_q) |
                      (capture[AsyncEv_BusEvents] ? bus_events_i : '0);
    end
  end

  // Events are cleared once they have been captured into the message buffer.
  logic [AsyncEv_Count-1:0] async_gnt;
  assign evt_captured = async_gnt;

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

    async_evt[AsyncEv_CCC].ccc = '{
      code:     AsyncEv_CCC,
      ccc:      i3c_ccc_e'(ccc_info.ccc),
      defb:     ccc_info.defb,
      has_defb: ccc_info.has_defb,
      default:  '0 // TODO: Implement `has_length` and `data_length` fields
    };

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
    async_evt[AsyncEv_TxSuspend].txds.targets = MaxTargets'(suspend_tx_q);

    async_evt[AsyncEv_IBISuspend].ibis.code = AsyncEv_IBISuspend;

    async_evt[AsyncEv_BusEvents].bus.code = AsyncEv_BusEvents;
    async_evt[AsyncEv_BusEvents].bus.evt  = bus_events_q;
  end

  // Report any failure to write into the Asynchronous Event Queue in a timely fashion.
  logic [AsyncEv_Count-1:0] evt_lost;
  assign evt_lost[AsyncEv_CCC]       = capture[AsyncEv_CCC]       && |ccc_targets &&
                                      !evt_captured[AsyncEv_CCC];
  assign evt_lost[AsyncEv_NotifyTx]  = capture[AsyncEv_NotifyTx]  && txd_result_q &&
                                      !evt_captured[AsyncEv_NotifyTx];
  assign evt_lost[AsyncEv_NotifyIBI] = capture[AsyncEv_NotifyIBI] && ibi_result_q &&
                                      !evt_captured[AsyncEv_NotifyIBI];
  // A bit already pending (buffered) that reasserts before being drained merges via OR, making the
  // new occurrence indistinguishable from the old one; report that loss. A bit that's newly set
  // (no overlap with what's already buffered) is not lost; it just joins the pending vector.
  assign evt_lost[AsyncEv_TxSuspend]  = capture[AsyncEv_TxSuspend]     &&
                                        |(suspend_tx_q & suspend_tx_i) &&
                                        !evt_captured[AsyncEv_TxSuspend];
  assign evt_lost[AsyncEv_BusEvents]  = capture[AsyncEv_BusEvents]     &&
                                        |(bus_events_q & bus_events_i) &&
                                        !evt_captured[AsyncEv_BusEvents];
  // A single boolean flag with no further structure has nothing more to lose from a repeat.
  assign evt_lost[AsyncEv_IBISuspend] = 1'b0;

  assign evt_lost_o = |evt_lost;

  // Arbitrate amongst the Asynchronous Event types.
  prim_arbiter_fixed #(
    .N         (AsyncEv_Count),
    .DW        ($bits(i3c_tti_async_event_t)),
    .EnDataPort(1)
  ) u_arb (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .req_i (async_req),
    .data_i(async_evt),
    .gnt_o (async_gnt),
    .idx_o (),

    // Write access to the queue.
    .valid_o(wvalid_o),
    .data_o (wdata_o),
    .ready_i(wready_i)
  );

  // TTI Async Event union size check.
  if ($bits(i3c_tti_async_event_t) != DataWidth) $fatal(2, "i3c_tti_async_event_t has incorrect size");

endmodule
