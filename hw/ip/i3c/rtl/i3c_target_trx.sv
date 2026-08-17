// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I3C Target transceiver.
//
// - Target (including Standby Controller) functionality.
// - This logic is reactive, responding to the SCL clock signal that it receives from the active
//   controller, and the word-level decoding is driven entirely by that clock before moving data
//   words and other signals across a CDC boundary into the main IP block.
// - Any command requiring an immediate response must also be implemented here, but data is
//   presented to this module preemptively by Target-side logic running within the main IP block
//   on its clock.
// - For Single Data Rate (SDR) communications, the input data (SDA) is sampled on the rising edge
//   of the clock (SCL) when receiving. Transmitted data is driven out on the SCL falling edge for
//   sampling by the Active Controller on the rising edge.
// - For Double Data Rate (HDR-DDR) communications, SDA is sampled or driven on both edge of SCL.
// - Together these two behaviors naturally lend themselves to the use of two shift registers,
//   one posedge-clocked and one negedge-clocked.
// - SDA is sampled into the LSB of each shift register, and driven out from the MSB.
// - Data is then loaded or read in parallel, without interleaving for SDR traffic, and with
//   interleaving for HDR-DDR.

module i3c_target_trx
  import i3c_io_pkg::*;
  import i3c_pkg::*;
  import i3c_target_pkg::*;
#(
  // Number of target(s) or target group(s) presented simultaneously on the I3C bus, including the
  // Standby Controller Role.
  parameter int unsigned NumTargets = 2,
  // Number of SDA lanes; must be one presently since HDR-BT mode not supported.
  parameter int unsigned NumSDALanes = 1
) (
  // No free-running clock from the IP block core; driven by controller-supplied SCL.
  // Asynchronous reset.
  input                     rst_ni,

  // TODO: Decide upon multi-cycle path/CDC/waiver here.
  // - these signals may be treated as quasi-static? Note, though, that they are modified in
  //   the target core in response to CCC traffic.
  // Target device descriptions.
  input  i3c_targ_dev_t     targ_dev_i[NumTargets],
  // Group address descriptions.
  input  i3c_grp_addr_t     grp_addr_i[NumGroups],
  // Blocked device addresses.
  // TODO: Both currently unused.
  input               [6:0] addr_blocked_i[NumBlocked],
  input               [6:0] mask_blocked_i[NumBlocked],

  // Transmit data for Private Read transfers.
  input                     trx_dvalid_i[NumTargets],
  output logic              trx_dready_o[NumTargets],
  input  i3c_targ_trx_txd_t trx_dreq_i[NumTargets],

  // Transmit for Direct Read CCCs.
  input                     trx_ctvalid_i,
  output logic              trx_ctready_o,
  input  i3c_targ_trx_txc_t trx_ctreq_i,

  // Arbitration request from the Target core.
  input                     trx_avalid_i,
  output                    trx_aready_o,
  input  i3c_targ_trx_arb_t trx_areq_i,

  // Received data to the Target core (Private Write transfers and CCC handling).
  output logic              trx_rtoggle_o,
  output i3c_targ_trx_rxd_t trx_rxd_o,

  // Status indications to Target core.
  output                    rep_start_det_o,
  output                    stop_det_o,
  output                    ddr_mode_o,

  // Start requests from the Target core.
  input                     sreq_sda_od_en_i,
  input                     sreq_sda_i,

  // HDR pattern detection.
  input                     hdr_exit_det_i,
  input                     hdr_restart_det_i,

  // I3C I/O signaling.
  input                     scl_i,
  input                     scl_ni,
  input                     sda0_clk_i,
  input                     sda0_clk_ni,
  input   [NumSDALanes-1:0] sda_i,
  output i3c_targ_bus_drv_t bus_drv_o,

  // Diagnostic visibility.
  output              [7:0] trx_state_o,
  output              [3:0] bus_mode_o,
  output              [6:0] te_o,

  // DFT-related controls.
  // TODO: Unused and can probably be removed.
  input                     scanmode_i
);

  import i3c_consts_pkg::*;
  import i3c_targ_ccc_pkg::*;
  import i3c_tti_pkg::*;

  // Bit index must count down from 8 to 0 for SDR data.
  // For HDR-DDR it must count down _pairs of bits_ from 9 to 0.
  localparam int unsigned BitW = 4;

  // Fault injection for testing Controllers.
  // TODO: Decide whether to keep this functionality.
  localparam bit FIParity = 1'b0;
  localparam bit FICRC5   = 1'b0;

  // Use token scheme to emit Double Data Rate signaling, rather than driving the MUX with the SCL
  // line directly.
  localparam bit UseTokens = 1'b1;

  logic start_det, stop_det;

  // Track whether we are currently in HDR-DDR mode.
  logic ddr_mode;

  // SDR sto(P) detection.
  always_ff @(posedge sda0_clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stop_det  <= 1'b0;
    end else if (start_det) begin
      stop_det  <= 1'b0;
    end else if (!ddr_mode) begin
      stop_det  <= scl_i;
    end
  end
  // The Target core, being clocked continually, must handle stoP detection.
  assign stop_det_o = stop_det;

  // Precondition for Repeated Start (Sr) detection.
  logic rep_start_pre;
  always_ff @(posedge sda0_clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rep_start_pre <= 1'b0;
    end else if (!ddr_mode) begin
      rep_start_pre <= !scl_i;
    end
  end

  // SDR (S)tart and Repeated Start detection.
  logic rep_start_det;
  always_ff @(posedge sda0_clk_ni or negedge rst_ni) begin
    if (!rst_ni) begin
      start_det     <= 1'b0;
      rep_start_det <= 1'b0;
    end else if (!ddr_mode) begin
      start_det     <= scl_i & !rep_start_pre;
      rep_start_det <= scl_i &  rep_start_pre;
    end
  end
  // The Target core needs informing of Repeated Starts too.
  assign rep_start_det_o = rep_start_det;

  // Parity and CRC-5 are calculated on all transmitted and received Command and Data Words in
  // HDR-DDR mode. When transmitting, the calculated values are inserted as the data is sent.
  logic [1:0] parity_q;
  logic [1:0] parity_d;
  logic [4:0] crc5_q;
  logic [4:0] crc5_d;
  logic parity_nq_emit;
  logic parity_pq_emit;
  logic crc5_nq_emit;
  logic crc5_pq_emit;

  // Arbitration requests.
  logic arb_starting;
  logic arb_won;  // TODO: This shall need to be persistent.
  // Sending IBI payload?
  logic ibi_sending;
  assign ibi_sending = 1'b0; // TODO: Missing implementation

  // Cede driving the bus
  logic drv_release;

  // Transmission of Read Data to the Controller.
  logic [8:0] tx_data_nq[NumSDALanes];
  logic [8:0] tx_data_pq[NumSDALanes];

  // Positive-edge data (transmission in HDR-DDR mode, reception in all modes).
  // - we have 9 data bits for each clock edge to support the collection of the lower 18 bits of
  //   the 20-bit HDR-DDR word; the 2 preamble bits have already steered the state machine and
  //   need not be preserved.
  // - similarly, when transmitting we inject the parity bits, so they do not need to be stored
  //   when parallel-loading the word.
  logic [8:0] sda_pq[NumSDALanes];
  logic sda_pq_shift;
  logic sda_pq_load;
  always_ff @(posedge scl_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sda_pq  <= '{'1};
    end else if (crc5_pq_emit) begin : crc5_pq
      // Load the odd-indexed bits of the CRC Word from the calculated CRC-5 value.
      // - park SDA high for bus turnaround.
      sda_pq[0][8:3] <= {1'b1, 1'b1, 1'b0, crc5_q[3], crc5_q[1], 1'b1};
    end else if (parity_pq_emit) begin : parity_pq
      sda_pq[0][8] <= parity_q[0];  // Driven from SCL-negedge flop.
    end else if (sda_pq_load) begin : load_pq
      for (int unsigned lane = 0; lane < NumSDALanes; lane++) begin
        sda_pq[lane]  <= tx_data_pq[lane];
      end
    end else if (sda_pq_shift) begin : shift_pq
      for (int unsigned lane = 0; lane < NumSDALanes; lane++) begin
        sda_pq[lane]  <= {sda_pq[lane][7:0], sda_i[lane]};
      end
    end
  end

  // Negative-edge data (reception in HDR-DDR mode, transmission in all modes).
  logic [8:0] sda_nq[NumSDALanes];
  logic sda_nq_shift;
  logic sda_nq_load;
  logic send_ack;
  always_ff @(posedge scl_ni or negedge rst_ni) begin
    if (!rst_ni) begin
      sda_nq  <= '{'1};
    end else if (send_ack) begin : ack_nq
      sda_nq[0][8] <= 1'b0;  // Explicitly drive a 0 bit onto the bus.
    end else if (crc5_nq_emit) begin : crc5_nq
      // Load the even-indexed bits of the CRC Word from the calculated CRC-5 value.
      sda_nq[0][8:3] <= {1'b0, 1'b1, 1'b0, crc5_q[4], crc5_q[2], crc5_q[0]};
    end else if (parity_nq_emit) begin : parity_nq
      sda_nq[0][8] <= parity_d[1];  // Driven from data because SCL-negedge flop not yet updated.
    end else if (sda_nq_load) begin : load_nq
      for (int unsigned lane = 0; lane < NumSDALanes; lane++) begin
        sda_nq[lane]  <= tx_data_nq[lane];
      end
    end else if (sda_nq_shift) begin : shift_nq
      for (int unsigned lane = 0; lane < NumSDALanes; lane++) begin
        sda_nq[lane]  <= {sda_nq[lane][7:0], sda_i[lane]};
      end
    end
  end

  // Collect the 8-bit SDR payload, excluding the Write Parity bit.
  logic [7:0] sdr_payload;
  assign sdr_payload = sda_pq[0][7:0];
  // Combine the SCL-posedge and SCL-negedge shift registers to present the received HDR-DDR word.
  // - `ddr_payload` and its derivative `cmd_word` are valid on the penultimate negative edge of the
  //   received data.
  i3c_ddr_cmd_word_t cmd_word;
  logic [15:0] ddr_payload;
  always_comb begin
    ddr_payload[15] = sda_pq[0][7];
    for (int unsigned b = 0; b < 7; b++) begin
      ddr_payload[2*b+2] = sda_nq[0][b];
      ddr_payload[2*b+1] = sda_pq[0][b];
    end
    // The LSB of the payload has not been captured at this point.
    ddr_payload[0] = sda_i[0];
  end
  // Reinterpret the HDR-DDR word.
  assign cmd_word = i3c_ddr_cmd_word_t'(ddr_payload);

  // The CCCs SETAASA and SETDASA shall be ignored by targets that already have a dynamic address.
  logic [NumTargets-1:0] targ_ignore_ccc;
  // Some CCCs shall be ignored at all times by all targets because they are unsupported.
  logic                  ignore_ccc;

  // Check whether the address matches against any of the configured target descriptions.
  logic            [6:0] addr_recvd;  // Target/Group being addressed.
  logic                  is_group;    // Is this a group address?
  logic    [TargIDW-1:0] targ_id;     // Individual Target addressed, _NoMatch or _Broadcast.
  logic [NumTargets-1:0] targ_set;    // Set of addressed target(s), valid for Group Addressing too.
  logic                  capture_all; // Capturing all traffic? TODO: Currently assigned but not used.
  always_comb begin : addr_matching
    // Disabled targets and those without a valid address shall ignore all traffic; i.e., they do
    // not even receive and respond to broadcast writes.
    logic [NumTargets-1:0] contenders;
    contenders = '0;
    for (int unsigned t = 0; t < NumTargets; t++) begin
      contenders[t] = targ_dev_i[t].en & targ_dev_i[t].addr_valid;
    end
    // Test the configured targets in descending order such that the first target has the
    // highest priority in the event of conflict. The first target may be the Standby Controller.
    targ_id     = TargIDNoMatch;
    targ_set    = '0;
    is_group    = 1'b0;
    capture_all = 1'b0;
    for (int t = NumTargets - 1; t >= 0; t--) begin
      if (contenders[t] && addr_recvd == targ_dev_i[t].addr && !targ_ignore_ccc[t]) begin
        targ_id     = TargIDW'(t);
        targ_set[t] = 1'b1;
      end
    end
    // Respond to the I3C Broadcast Address; this commences I3C Common Command Codes as well as
    // Private Read/Write operations.
    if (addr_recvd == Addr_Broadcast) begin
      targ_id  = TargIDBroadcast;
      targ_set = contenders;
    end else begin
      // Test the group addresses.
      // - as a diagnostic feature, a group address of zero matches against all observed traffic.
      for (int g = NumGroups - 1; g >= 0; g--) begin
        if (grp_addr_i[g].addr_valid &&  // Group configured?
           ((addr_recvd == grp_addr_i[g].addr && !ignore_ccc) || ~|grp_addr_i[g].addr)) begin
          targ_set = grp_addr_i[g].targets[NumTargets-1:0] & contenders;
          targ_id  = TargIDNoMatch;
          is_group = 1'b1;
          capture_all = ~|grp_addr_i[g].addr;
        end
      end
    end
  end

  // Properties of the current transfer.
  // - these properties are persistent and may be used during transfer processing.
  struct packed {
    logic     [TargIDW-1:0] targ_id;   // Target ID (this is _not_ the I3C Address).
    logic  [NumTargets-1:0] targ_set;  // Set of addressed targets, supporting Group Addresses too.
    logic             [6:0] addr;      // Addressed target/group.
    logic                   is_group;  // Is this a group address?
    logic                   rnw;       // Read, not Write, for Private transfers or CCC segments.
    logic             [7:0] cmd;       // (i) Command or (ii) CCC, including `Direct` flag in MSB.
    // Note: the 'Defining Byte' here means a data byte after the CCC and before the Sr; for some
    //       CCCs such as ENEC/DISEC this is strictly not called a Defining Byte in the spec.
    logic                   has_defb;  // Indicates whether a Defining Byte has been received.
    logic             [7:0] defb;      // Defining Byte, if any, for CCC handling.
  } trans;

  i3c_targ_ccc_state_e ccc_state_q;
  logic [3:0] ccc_idx_q;

  // Is there a CCC Command in progress on the I3C bus?
  wire ccc_command = !(ccc_state_q inside {CCC_Idle, CCC_Private, CCC_Setup});
  // A Repeated Start continues a Direct CCC transfer only when one is actually in progress.
  wire ccc_continues = (ccc_state_q == CCC_Setup && !broadcast_ccc(trans.cmd)) ||
                       (ccc_state_q inside {CCC_SegAddr, CCC_SegData});
  // Receiving a Common Command Code byte itself?
  wire is_ccc = (ccc_state_q == CCC_Setup) & ~|ccc_idx_q;
  // Is this address header within a CCC segment?
  wire ccc_addr_seg = (ccc_state_q == CCC_SegAddr);

  always_comb begin
    // Some CCCs shall be ignored entirely; unsupported Direct CCCs shall be NACKed.
    // - Note: Broadcast CCCs should not be followed by a non-Broadcast address post-Sr.
    ignore_ccc = (ccc_state_q == CCC_SegAddr) && !supported_direct_ccc(trans.cmd);
    // The CCCs SETAASA and SETDASA shall be ignored by targets that already have a dynamic address.
    // TODO: The SETxASA handling is probably best handled outside of this module and in the system
    //       clock domain.
    for (int unsigned t = 0; t < NumTargets; t++) begin
      targ_ignore_ccc[t] = &{ccc_state_q == CCC_SegAddr, trans.cmd inside {SETAASA, SETDASA},
                             targ_dev_i[t].addr_valid, targ_dev_i[t].addr_dynamic} | ignore_ccc;
    end
  end

  // Target ID; this is either the unique ID number of a configured Target, or zero, to ensure it
  // can be safely used as index into all data structures that have `NumTargets` entries.
  logic [TargIDW-1:0] sel_targ_id;
  assign sel_targ_id = (trans.targ_id < NumTargets) ? trans.targ_id : '0;

  // Read data has been presented in anticipation of HDR-DDR transmission, but it may be collected
  // in SDR mode.
  function automatic logic [8:0] extract_data_nq(logic [8:0] data_nq, logic [8:0] data_pq,
                                                 logic last, logic ddr);
    logic [8:0] tx_data_nq;
    // For HDR-DDR, odd-indexed bits are SCL-negedge clocked, i.e. including the MSB.
    if (ddr) tx_data_nq = data_nq;
    else begin
      // SDR transmission requires us to interleave the bits from 'pq' and 'nq', but we're also
      // collecting the first byte from the HDR-DDR Data Word, so it's located in the MSBs.
      for (int unsigned b = 0; b < 4; b++) begin
        tx_data_nq[2*b+1] = data_pq[b+4];
        tx_data_nq[2*b+2] = data_nq[b+4];
      end
      tx_data_nq[0] = !last;
    end
    return tx_data_nq;
  endfunction

  // Transmission data may come from a few sources:
  // - per-Target Private Read inputs
  // - per-Target inputs for Direct Read CCCs.
  // - arbitration phase; transmit address.
  // - In-Band Interrupt data payload.
  logic sel_valid;
  always_comb begin : gen_tx_data
    logic [8:0] data_nq;
    logic [8:0] data_pq;
    logic rlast;

    sel_valid = (trans.targ_id < NumTargets) & (ccc_command ? trx_ctvalid_i
                                                            : trx_dvalid_i[sel_targ_id]);
    data_nq = ccc_command ? trx_ctreq_i.rdata_nq[sel_targ_id] : trx_dreq_i[sel_targ_id].rdata_nq;
    data_pq = ccc_command ? trx_ctreq_i.rdata_pq[sel_targ_id] : trx_dreq_i[sel_targ_id].rdata_pq;
    rlast   = ccc_command ? trx_ctreq_i.rlast[sel_targ_id][0] : trx_dreq_i[sel_targ_id].rlast[0];

    // For Arbitrable Address Headers and In-Band Interrupts, we drive SDA on the SCL negedge.
    // For HDR-DDR, odd-indexed bits are SCL-negedge clocked, i.e. including the MSB.
    // For SDR transmission, all bits are transmitted on the SCL negedge.
    tx_data_nq[0] = arb_starting ? {trx_areq_i.addr, trx_areq_i.ibi, 1'b0} :
                    (ibi_sending ? trx_areq_i.rdata_nq
                                 : extract_data_nq(data_nq, data_pq, rlast, ddr_mode));
    // For HDR-DDR, even-indexed bits are SCL-posedge clocked, i.e. including the LSB.
    tx_data_pq[0] = data_pq;
  end

  typedef enum logic [4:0] {
    State_Idle,
    State_PreStop,

    // --- Address arbitration ---
    State_ArbCont,  // Still a contender.
    State_ArbCede,  // Ceded bus, or did not contend.
    State_AckAddr,

    // --- Single Data Rate (SDR) traffic ---
    State_RxSDR,
    State_TxSDR,
    State_WaitStop,

    // --- Double Data Rate (HDR-DDR) Transmission ---
    State_TxPreDDR,
    State_TxDataDDR,
    State_TxCRCDDR,
    State_TxNACKDDR,  // TODO: Implement this state; send `11`.

    // --- HDR-DDR Reception ---
    // TODO: ACK/NACK of command (first data word).
    // TODO: Must respond to Controller abort of read Data Word.
    State_RxCmdDDR,
    State_RxPreDDR,
    State_RxDataDDR,
    State_RxCRCDDR,
    State_RxRsvdDDR,

    // --- Ignoring traffic, e.g., HDR mode that is not understood, or Target Errors. ---
    State_Ignore
  } state_e;

  // Transceiver state.
  state_e state_q, state_d;
  logic [BitW-1:0] bit_idx;
  // Is the current bit within the payload? Applies to Command and Data Words.
  wire data_bit = (|bit_idx && bit_idx <= 'h8);
  // Indications of pre-penultimate, penultimate and the last bit; these are useful for both
  // the addressing phase and the reception of HDR-DDR words.
  wire prepen_bit = (bit_idx == BitW'('d2)); // currently unused
  wire penult_bit = (bit_idx == BitW'('d1));
  wire last_bit = ~|bit_idx;

  // There are a number of forms of addressing:
  // - SDR Address Header; Target address or Group address.
  // - HDR-DDR Command Word.
  assign addr_recvd = (state_q == State_RxCmdDDR) ? cmd_word.targ_addr
                                                  : sda_pq[0][7:1];  // RnW already captured.

  // Transmitting during arbitration phase?
  wire tx_arb = (state_q == State_ArbCont);
  // Transmitting in SDR mode?
  wire tx_sdr = (state_q == State_TxSDR);

  // Receiving data on both clock edges?
  wire rx_ddr = state_q inside {State_RxCmdDDR, State_RxPreDDR, State_RxDataDDR, State_RxCRCDDR,
                                State_RxRsvdDDR};
  // Transmitting data on both clock edges?
  wire tx_ddr = state_q inside {State_TxPreDDR, State_TxDataDDR, State_TxCRCDDR, State_TxNACKDDR};

  logic rx_enthdr, enthdr_det, entddr_det;
  logic [7:0] rx_ccc;

  // Track whether the bus is in DDR mode; this is especially important in deactivating the Start
  // and stoP detectors since SDA transitions are _required_ with SCL high during HDR-DDR.
  logic [3:0] bus_mode_nq;  // MSB set indicates transition into one of the HDR modes.
  always_ff @(posedge scl_ni or negedge rst_ni) begin
    if (!rst_ni) bus_mode_nq <= '0;
    else if (state_q == State_RxSDR && enthdr_det) begin
      // Although we support only HDR-DDR mode, it is useful to report other HDR modes to software.
      bus_mode_nq <= {1'b1, rx_ccc[2:0]};
    end else bus_mode_nq <= '0;
  end
  // Track the current bus mode.
  logic [3:0] bus_mode_pq;
  always_ff @(posedge scl_i or negedge rst_ni) begin
    if (!rst_ni) bus_mode_pq <= '0;
    else if (hdr_exit_det_i) bus_mode_pq <= 4'h0;  // Return to SDR mode.
    else if (bus_mode_nq[3]) bus_mode_pq <= bus_mode_nq;
  end
  assign ddr_mode = (bus_mode_pq == 4'h8);  // ENTHDR0 (HDR-DDR mode).

  // Export transceiver state and bus mode for diagnostic visibility.
  assign trx_state_o = 8'(state_q);
  assign bus_mode_o  = bus_mode_pq;

  // Arbitration is lost if we're requesting a '1' but the line was pulled to '0'.
  wire arb_lost = bus_drv_o.sda[0] & !sda_pq[0][0];

  // TODO: This will need to be latched and perhaps sent with a toggle.
  assign arb_won = &{(state_q == State_ArbCont), penult_bit, !arb_lost};

  // Shall we arbitrate on the bus when Start signaling is detected?
  // - Note: arbitration is not permitted for Repeated Starts (Sr).
  wire arb_reqd = trx_avalid_i;
  assign trx_aready_o = arb_won;

  // There are two reasons for detecting a mismatch between the observed SDA state and the SDA
  // state that we are trying to achieve:
  // - Arbitrable Address headers; we may have lost the arbitration.
  // - Contention on the SDA line, which we need to detect in order to invoke recovery procedures.
  logic sda_diff;

  logic [2:0] started;
  always_ff @(posedge scl_ni or negedge rst_ni) begin
    if (!rst_ni) started <= '0;
    else started <= {stop_det, rep_start_det, start_det};
  end

  wire starting     = start_det     & !started[0];
  wire rep_starting = rep_start_det & !started[1];
  wire stopping     = stop_det      & !started[2];

  assign arb_starting = starting & arb_reqd;
  // Release the bus whenever we are no longer entitled to drive it: we lost arbitration, we won
  // the Arbitrable Address Header (the Active Controller drives the ACK, not us), or we are
  // ignoring the remainder of the frame.
  assign drv_release = state_q inside {State_Idle, State_WaitStop, State_Ignore} ||
                       ((state_q == State_ArbCont) && (arb_lost || penult_bit));

  // Is there something to transmit on behalf of the addressed target?
  wire tx_avail = sel_valid;

  // In SDR transmission there may be data already available for a subsequent transmission; we must
  // consult the current state of SDA, which indicates the agreement between Target and Controller
  // as to whether transmission shall continue.
  ///
  // Also, as a safety measure, we stop transmitting if we have indicated that there is no more
  // data, whatever we happen to sample.
  wire tx_sdr_ending = ~&{sda_nq[0][8], sda_i[0], tx_avail};

  // Starting transmission of a new data unit.
  wire tx_starting = &{tx_avail, trans.rnw, last_bit,
                       |{state_q inside {State_AckAddr, State_RxCmdDDR, State_TxDataDDR},
                         state_q == State_TxSDR & !tx_sdr_ending}};

  // Ending transmission of the current data unit (Note: may also be starting another).
  wire tx_ending = last_bit & |{state_q inside {State_AckAddr, State_TxCRCDDR},
                                state_q == State_TxSDR & tx_sdr_ending};
  assign sda_nq_load = arb_starting | tx_starting;

  // SCL-positive shift register must be loaded, shifted etc. a half-cycle later for HDR-DDR.
  logic sda_pq_mismatch;
  always_ff @(posedge scl_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sda_pq_mismatch <= 1'b0;
      sda_pq_load     <= 1'b0;
      crc5_pq_emit    <= 1'b0;
      parity_pq_emit  <= 1'b0;
    end else begin
      sda_pq_mismatch <= sda_diff;
      sda_pq_load     <= sda_nq_load & ddr_mode;
      crc5_pq_emit    <= crc5_nq_emit;
      parity_pq_emit  <= parity_nq_emit;
    end
  end

  // TODO: Decide whether we can save some power here, gating on transmit/receive activity for
  // SDR traffic. For HDR-DDR I guess we just have to clock both on every clock edge.
  // There are `tx_supply` and `rx_sample` signals available already; these may be useful.
  // Perhaps we can also disable the shifter if we're ignoring traffic, e.g. communication with
  // other targets or HDR modes that we don't understand.
  assign sda_pq_shift = 1'b1;
  assign sda_nq_shift = 1'b1;

  assign rx_ccc = sda_pq[0][8:1];

  // There are 8 HDR modes and we must have awareness of all such modes, though we presently
  // implement only HDR-DDR. Traffic in other HDR modes must be ignored until HDR Exit is detected.
  assign rx_enthdr = (rx_ccc[7:3] == (ENTHDR0 >> 3));
  assign enthdr_det = &{is_ccc, last_bit, rx_enthdr};
  assign entddr_det = &{is_ccc, last_bit, rx_ccc == ENTHDR0};

  // Preamble bits at the start of HDR-DDR word.
  wire [1:0] ddr_pre = {sda_pq[0][0], sda_i[0]};

  // Has the Controller requested that a transmission (SDR/HDR-DDR Read) be aborted?
  // TODO: Needs qualifying with knowledge of whether this is the first data word in the HDR-DDR
  // transmission because PRE0 has the opposite sense for the first word, in order to support an
  // ACK/NACK response from the Target.
  wire tx_abort = 1'b0 & !ddr_pre[0];

  // We need to make a decision on whether to ACK/NACK; this depends upon the address received,
  // whether it's a Broadcast, and whether we can return read data.
  logic ack_addr;
  always_comb begin
    // sda_i[0] is the RnW bit at this point.
    case (targ_id)
      TargIDNoMatch:   ack_addr = !sda_i[0] & |targ_set;  // Group Addresses accept only Writes.
      TargIDBroadcast: ack_addr = !sda_i[0];  // Writes only.
      // TODO: We should have an indication at this point whether we are able to accept any write
      // data; we at least need a Rx descriptor slot and one Rx DWORD really, but after that we
      // must junk data.
      default: ack_addr = !sda_i[0] |
                         ((targ_id < NumTargets) & (ccc_addr_seg ? trx_ctvalid_i
                                                                 : trx_dvalid_i[targ_id]));
    endcase
  end
  assign send_ack = &{state_q == State_ArbCede, penult_bit, ack_addr};

  // Detection of Error Type TE0 (4.3.8.1.1).
  assign te_o[0]   = &{state_q == State_ArbCede, penult_bit, te0_invalid_addr(addr_recvd)};
  // TODO: Te1-TE6 are not yet detected.
  assign te_o[6:1] = '0;

  // CCCs that are not understood shall be NACKed if they are not Broadcasts.
  // TODO: The NACK 'generation'. There are also some rules about Defining Bytes and payload bytes
  // to be implemented here.
  // nack = ~{broadcast_ccc(ccc_req_i.rdata), supported_direct_ccc(ccc_req_i.rdata)};

  // Arbitration loss or driver conflict on SDA line, including any mismatch detected during the
  // preceding clock phase (important for HDR-DDR).
  wire sda_mismatch = sda_pq_mismatch | sda_diff; // TODO: Currently unused

  // State advances only on the falling edge of controller-supplied SCL, which represents the
  // reception or transmission of either 1 bit (SDR) or 2 bits (HDR-DDR) per SDA lane.
  always_comb begin
    state_d = state_q;
    // TODO: HDR Exit detection must be responsive at all times, but it is perhaps the Target core
    // that needs to respond.
    if (starting) begin
      // START handling.
      state_d = arb_reqd ? State_ArbCont : State_ArbCede;
    end else if (rep_starting) begin
      state_d = State_ArbCede;
    end else begin
      case (state_q)
        // --- Address Arbitration ---
        State_ArbCont: state_d = penult_bit ? (ack_addr ? State_AckAddr : State_WaitStop)
                                            : (arb_lost ? State_ArbCede : State_ArbCont);
        State_ArbCede: state_d = penult_bit ? (ack_addr ? State_AckAddr : State_WaitStop)
                                            : State_ArbCede;
        // The Active Controller's ACK/NACK of an Arbitrable Address Header is sampled on the rising
        // edge within the ACK bit. On the addressed-target path we drive that bit low ourselves, so
        // the same test covers both cases and also catches a driver conflict on the ACK bit.
        State_AckAddr: state_d = sda_pq[0][0] ? State_WaitStop
                                              : (trans.rnw ? State_TxSDR : State_RxSDR);

        // --- Receiving in SDR mode ---
        State_RxSDR: begin
          // We must detect entry to any HDR mode, though we understand only HDR-DDR.
          state_d = entddr_det ? State_RxCmdDDR : (enthdr_det ? State_Ignore : State_RxSDR);
        end
        // --- Transmitting in SDR mode ---
        State_TxSDR: state_d = (last_bit & tx_sdr_ending) ? State_WaitStop : State_TxSDR;
        // --- Ignoring SDR traffic, awaiting stoP or Sr ---
        State_WaitStop: state_d = State_WaitStop;  // stoP and repeated Start are handled above.

        // --- Expecting an HDR-DDR Command word ---
        // TODO: Check the expected 2'b01 preamble; what do we do if we get something else?
        //       I think this is a case of waiting for HDR Restart/Exit.
        State_RxCmdDDR: begin
          // Respond to Read/Write Command, considering whether or not there is data available.
          // - NACKing of Read Commands is always permitted.
          // - NACKing of Write Commands may be enabled, but is not permitted by default.
          // TODO: State_TxNACKDDR is not implemented yet and causes unintended partial transfers
          state_d = last_bit ? (trans.rnw ? (tx_avail ? State_TxPreDDR : State_TxNACKDDR)
                                          : State_RxPreDDR)
                             : State_RxCmdDDR;
        end
        // --- Expecting an HDR-DDR Data Word or CRC word ---
        State_RxPreDDR:
          case (ddr_pre)
            2'b00:   state_d = State_RxRsvdDDR;
            2'b01:   state_d = State_RxCRCDDR;
            default: state_d = State_RxDataDDR;
          endcase
        State_RxDataDDR: state_d = last_bit ? State_RxPreDDR : State_RxDataDDR;
        State_RxCRCDDR:  state_d = last_bit ? State_RxCmdDDR : State_RxCRCDDR;
        State_RxRsvdDDR: state_d = last_bit ? State_RxPreDDR : State_RxRsvdDDR;
        // --- Word Transmission ---
        // TODO: We have the option here of transmitting the CRC following the Controller's Abort.
        State_TxPreDDR:  state_d = tx_abort ? State_RxCmdDDR : State_TxDataDDR;
        State_TxDataDDR: state_d = last_bit ? (tx_avail ? State_TxPreDDR : State_TxCRCDDR)
                                            : State_TxDataDDR;
        State_TxCRCDDR:  state_d = last_bit ? State_RxCmdDDR : State_TxCRCDDR;
        // --- Ignoring traffic that is not understood; other HDR modes and Target Errors. ---
        State_Ignore:    state_d = hdr_exit_det_i ? State_Idle : State_Ignore;
        // --- Recovery from invalid states ---
        default:         state_d = State_Idle;
      endcase
    end
  end

  // Target state machine.
  // TODO: Q: Do we need to track whether this is the first data word associated with a command,
  // esp. read commands?
  always_ff @(posedge scl_ni or negedge rst_ni) begin
    if (!rst_ni) state_q <= State_Idle;
    else state_q <= state_d;
  end

  // CCC tracking.
  //
  // - Processing of CCCs is not performed here, to limit the amount of logic that is clocked
  //   on SCL directly, but the CCC framing into setup and read/write segments is tracked.
  // - We need to track the current bus mode (e.g. SDR -> HDR-DDR) without the delays of two
  //   clock domain crossings.
  // - Note: though some effort was expended here at handling CCCs in HDR-DDR mode, the reality
  //   appears to be that nothing but the base specification (I3C Basic) actually supports them.
  //
  // TODO: This logic may become complex enough that it should be migrated into a submodule.
  always_ff @(posedge scl_ni or negedge rst_ni) begin
    if (!rst_ni) begin
      trans           <= '0;
      trans.targ_id   <= TargIDNoMatch;
      ccc_state_q     <= CCC_Idle;
      ccc_idx_q       <= '0;
    end else begin
      // TODO: Need to check that these conditions become appropriately deasserted.
      if (starting || stopping || (rep_starting && !ccc_continues)) begin
        // CCC has ended, or was never in progress.
        trans.cmd       <= '0;
        trans.targ_id   <= TargIDNoMatch;
        trans.has_defb  <= 1'b0;
        ccc_state_q     <= CCC_Idle;
        ccc_idx_q       <= '0;
      end else if (rep_starting) begin
        // Next phase of Direct CCC may address another Target/Group.
        ccc_state_q <= CCC_SegAddr;
        ccc_idx_q   <= '0;
      end else begin
        // Capture important data because `sdr_payload` or `ddr_payload` is available, but do _not_
        // commit to a state change at this point because the parity has not been checked.
        if (penult_bit) begin
          case (state_q)
            State_ArbCont,
            State_ArbCede: begin
                trans.targ_id   <= targ_id;
                trans.targ_set  <= targ_set;
                trans.is_group  <= is_group;
                trans.addr      <= addr_recvd;
                trans.rnw       <= sdr_payload[0];
              end

            State_RxSDR:
              case (ccc_state_q)
                CCC_Setup:
                  case (ccc_idx_q)
                    4'd0: trans.cmd <= sdr_payload;          // The Common Command Code.
                    4'd1: if (ccc_has_defb(trans.cmd)) begin // Only CCCs that actually define one.
                      trans.defb     <= sdr_payload;
                      trans.has_defb <= 1'b1;
                    end
                    default: ; // Payload bytes; do not disturb `trans`.
                  endcase
                default: begin end
              endcase

            State_RxCmdDDR:
              case (ccc_state_q)
                CCC_Idle: begin
                  // Target ID here determines whether this is CCC framing or a Private transfer.
                  trans.targ_id   <= targ_id;
                  trans.targ_set  <= targ_set;
                  trans.is_group  <= is_group;
                  trans.addr      <= addr_recvd;
                  trans.rnw       <= ddr_payload[15];
                  // Capture the command for Private Read/Write, includes R/nW bit.
                  trans.cmd       <= ddr_payload[15:8];
                end
                CCC_Setup: begin
                  // Common Command Code; bit 15 indicates Direct (1) rather than Broadcast (0).
                  trans.cmd     <= ddr_payload[15:8];
                end
                CCC_SegAddr: begin
                  // A Broadcast address here signals termination of a the previous CCC and
                  // commencement of a new CCC transfer.
                  if (cmd_word.targ_addr == Addr_Broadcast && cmd_word.rnw) begin
                    ccc_state_q <= CCC_Setup;
                  end
                end
                default: begin end
              endcase

            State_RxDataDDR:
              case (ccc_state_q)
                CCC_Setup: begin
                  // Capture the Common Command Code and Defining Byte, if any.
                  trans.cmd   <= ddr_payload[15:8];
                  trans.defb  <= ddr_payload[7:0];
                end
                CCC_SegAddr: begin
                  trans.rnw       <= cmd_word.rnw;
                  trans.targ_id   <= targ_id;
                  trans.targ_set  <= targ_set;
                  trans.is_group  <= is_group;
                  trans.addr      <= addr_recvd;
                end
                default: begin end
              endcase

            default: begin end
          endcase
        end

        // Confirm validity of received data and perform state transition.
        if (last_bit) begin
          case (state_q)
            State_AckAddr: begin
              if (trans.targ_id == TargIDBroadcast && !trans.rnw) begin
                ccc_state_q <= CCC_Setup;
              end else begin
                // Next segment/phase within the same CCC transfer?
                case (ccc_state_q)
                  CCC_SegAddr: ccc_state_q <= CCC_SegData;
                  default:     ccc_state_q <= CCC_Private;
                endcase
              end
              ccc_idx_q <= '0;
            end

            State_RxSDR: begin
              case (ccc_state_q)
                CCC_Setup:
                  // ENTHDRx CCCs do not follow the normal pattern; no Sr expected.
                  if (enthdr_det) ccc_state_q <= CCC_Idle;
                  else ccc_idx_q <= ccc_idx_q + ~&ccc_idx_q;
                CCC_SegAddr: begin
                  if (|trans.targ_set) begin
                    ccc_state_q <= CCC_SegData;
                    ccc_idx_q <= 'b0;
                  end else ccc_idx_q <= ccc_idx_q + ~&ccc_idx_q;
                end
                CCC_SegData: ccc_idx_q <= ccc_idx_q + ~&ccc_idx_q;
                default: begin end
              endcase
            end

            State_RxCmdDDR: begin
              case (ccc_state_q)
                CCC_Idle: begin
                  // TODO: HDR-DDR CCC framing is not yet supported; the Indicator Word is treated
                  // as a Private transfer. `trans.targ_id` (not the stale combinational `targ_id`)
                  // is the correct test to use for future implementations - see 6.2.3.3.1.1.
                  ccc_state_q <= CCC_Private;
                end
                CCC_Setup: begin
                  ccc_idx_q   <= ccc_idx_q + 'b10;
                  ccc_state_q <= CCC_SegAddr;
                end
                CCC_SegAddr: ccc_state_q <= CCC_SegData;
                default: begin end
              endcase
            end

            default: begin end
          endcase
        end
      end
    end
  end

  // Supply new data on SDA?
  wire transmitting = |{tx_arb, tx_sdr, tx_ddr};
  wire tx_supply = transmitting;
  // Sample the current state of SDA?
  wire rx_sample = rx_ddr || (state_q inside {State_ArbCont, State_ArbCede, State_RxSDR});
  wire buf_shift = tx_supply | rx_sample;

  // Bit pair used to update the parity and CRC-5 calculations.
  // - When transmitting, the pair is taken from the two shift registers.
  // - For HDR-DDR reception the pair comprises the odd-indexed bit, sampled on the preceding SCL
  //   rising edge, and the even-indexed bit presently on SDA, which is sampled by this edge.
  // - For SDR reception there is a single bit per SCL cycle and it is folded into both halves, such
  //   that `parity_q[0]` accumulates the running odd parity of the byte. Take it from the shift
  //   register that is sampled on the SCL rising edge, where the Controller guarantees the data to
  //   be stable.
  wire [1:0] parcrc_bit = transmitting ? {sda_nq[0][8], sda_pq[0][8]} :
                          (rx_ddr      ? {sda_pq[0][0], sda_i[0]}
                                       : {sda_pq[0][0], sda_pq[0][0]});

  // Parity calculated on received/transmitted data.
  logic       parity_sdr; // TODO: Currently unused
  logic       upd_parity;
  logic       init_parity;
  assign parity_d = {(parity_q[1] & ~init_parity) ^ parcrc_bit[1],
                     (parity_q[0] |  init_parity) ^ parcrc_bit[0]};
  // For reception of SDR Write data it suffices to consult only the first parity bit, which
  // is the XOR of all received data bits, XORed with '1'.
  assign parity_sdr = parity_q[0];
  // Parity has no history from one data unit to the next, so we just need to initialize it on the
  // first data bit (SDR) or bit pair (HDR-DDR) of each word; both arrive at `bit_idx` == 8.
  assign init_parity = (bit_idx == BitW'(8));
  assign upd_parity = data_bit & (state_q inside {State_RxCmdDDR, State_RxDataDDR, State_TxDataDDR,
                                                  State_RxSDR});


  // CRC-5 calculated on received/transmitted data.
  logic init_crc, upd_crc;
  assign crc5_d = init_crc ? '1 : {crc5_q[2],
                                   crc5_q[1] ^ parcrc_bit[1] ^ crc5_q[4],
                                   crc5_q[0] ^ parcrc_bit[0] ^ crc5_q[3],
                                   crc5_q[4] ^ parcrc_bit[1],
                                   crc5_q[3] ^ parcrc_bit[0]};
  assign init_crc = (state_q == State_RxCmdDDR && bit_idx > 'h8);
  assign upd_crc  = (state_q inside {State_RxCmdDDR, State_RxDataDDR, State_TxDataDDR}) & data_bit;

  // Do the calculated parity and CRC-5 values match against the received values?
  // TODO: Can we defer the parity checking slightly, to avoid the combinational signal
  // `parity_error_ddr` briefly becoming asserted and causing confusion?
  wire parity_match_ddr = (parcrc_bit == parity_q);
  wire parity_check_ddr = (state_q == State_RxCmdDDR || state_q == State_RxDataDDR) && last_bit;
  wire parity_error_ddr = parity_check_ddr && !parity_match_ddr;

  // I3C SDR Write data uses odd parity, so the received T bit should equal `parity_sdr`.
  // - the T bit is sampled into the shift register on the SCL rising edge within its own bit period.
  wire parity_match_sdr = (sda_pq[0][0] == parity_sdr);
  wire parity_check_sdr = (state_q == State_RxSDR) && last_bit;
  wire parity_error_sdr = parity_check_sdr && !parity_match_sdr;

  wire crc5_match = ({sda_pq[0][2], sda_nq[0][1], sda_pq[0][1],
                      sda_nq[0][0], sda_pq[0][0]} == crc5_q);
  wire crc5_check = (state_q == State_RxCRCDDR && last_bit);
  wire crc5_error = crc5_check & !crc5_match;

  // Transmission of parity and CRC_5.
  assign parity_nq_emit = (state_q == State_TxDataDDR) & penult_bit;
  // TODO: We shall also need to respond to an explict 'last datum' indicator.
  assign crc5_nq_emit = (state_q == State_TxDataDDR) & last_bit & !tx_avail;

  // Bit counting within data unit, and calculation of parity/CRC-5 on the data bits.
  logic rx_sample_q; // TODO: Currently unused
  always_ff @(posedge scl_ni or negedge rst_ni) begin
    if (!rst_ni) begin
      crc5_q        <= '1;
      parity_q      <= 2'b01;
      bit_idx       <= '1;
      rx_sample_q   <= 1'b0;
    end else begin
      if (starting | rep_starting) begin
        bit_idx <= BitW'(8);
      end else if (last_bit) begin
        case (state_q)
          // SDR traffic shall be followed by further SDR traffic or, if entering HDR-DDR mode,
          // a Command Word.
          State_RxSDR:     bit_idx <= entddr_det ? BitW'(9) : BitW'(8);
          // DDR signaling counts down two bits at a time and should be zero for the final pair of
          // bits, which will be collected on the SCL negative edge, so we initialize to 'bits'/2-1.
          State_RxCmdDDR:  bit_idx <= BitW'(0);  // Preamble next.
          State_RxPreDDR:  bit_idx <= (ddr_pre == 2'b01) ? BitW'(4) : BitW'(8);
          State_RxDataDDR,
          State_RxRsvdDDR: bit_idx <= BitW'(0);  // Preamble next.
          State_TxPreDDR:  bit_idx <= BitW'(8);
          State_TxDataDDR: bit_idx <= tx_avail ? BitW'(0) : BitW'(5);
          // After a CRC Word in either direction, a command is expected, unless signaling is
          // interrupted by HDR Restart/Exit.
          State_RxCRCDDR,
          State_TxCRCDDR:  bit_idx <= BitW'(9);
          default:         bit_idx <= BitW'(8);
        endcase
      end else begin
        bit_idx   <= bit_idx - BitW'(buf_shift);
      end

      // Conditionally update CRC-5 and parity.
      if (init_crc | upd_crc) crc5_q <= crc5_d ^ {3'b0, FICRC5, 1'b0};
      if (init_parity | upd_parity) parity_q <= parity_d ^ {1'b0, FIParity & parity_d[0]};

      rx_sample_q   <= rx_sample & ~|bit_idx;
    end
  end

  // Output driver enables.
  //   (Normally driven on the SCL negative edge in SDR mode, like SDA itself.)
  //
  // Note: There's a complication here that we need to let SDA become Hi-Z on rising SCL for SDR
  // read T-bit.
  logic sda_pp_en_nq, sda_od_en_nq;
  always_ff @(posedge scl_ni or negedge rst_ni) begin
    if (!rst_ni) begin
      // Disable drivers.
      sda_pp_en_nq  <= 1'b0;
      sda_od_en_nq  <= 1'b0;
    end else if (arb_starting | send_ack) begin
      // Starting arbitration or Acknowledge SDR address.
      sda_pp_en_nq  <= 1'b0;
      sda_od_en_nq  <= 1'b1;
    end else if (drv_release) begin
      // Disable drivers when arbitration cannot proceed or is completed.
      sda_pp_en_nq  <= 1'b0;
      sda_od_en_nq  <= 1'b0;
    end else if (tx_starting | tx_ending) begin
      sda_pp_en_nq  <= tx_starting;
      sda_od_en_nq  <= 1'b0;
    end
  end

  // Disable push-pull driver on SCL rising edge.
  wire sdr_tx_t = (state_q == State_TxSDR) & last_bit;

  // Ensure that the we set SDA to Hi-Z for SDR read T-bit.
  logic sda_pp_en_pq, sda_od_en_pq;
  always_ff @(posedge scl_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sda_pp_en_pq  <= 1'b0;
      sda_od_en_pq  <= 1'b0;
    end else begin
      sda_pp_en_pq  <= sda_pp_en_nq & !sdr_tx_t;
      sda_od_en_pq  <= sda_od_en_nq;
    end
  end

  // ------------------------------------ I3C Data Output ------------------------------------------
  if (UseTokens) begin : gen_use_tokens
    // We use a single-bit toggle that counts the even and odd clock _cycles_, and by propagating
    // the current toggle state through the rising edge of SCL we can know which of the pair of
    // data bits should be driving the SDA line in HDR-DDR transmission.
    //
    // Propagate the toggle bit to the SCL-falling logic.
    logic sda_out_ptog;
    always_ff @(posedge scl_i or negedge rst_ni) begin
      if (!rst_ni) sda_out_ptog  <= 1'b0;
      else if (!transmitting) sda_out_ptog  <= 1'b0;
      else sda_out_ptog <= ddr_mode ^ sda_out_ptog;  // Reduce the chance of glitches in SDR mode.
    end
    // SCL-falling logic captures the new toggle bit and switches over to emitting the
    // even-indexed bit.
    logic sda_out_ntog;
    always_ff @(posedge scl_ni or negedge rst_ni) begin
      if (!rst_ni) sda_out_ntog <= 1'b0;
      else if (!transmitting) sda_out_ntog <= 1'b0;
      else sda_out_ntog <= sda_out_ptog;
    end

    // Use the toggle mismatch to determine the clock phase, observing that in SDR mode only the
    // SCL-negedge bits are used (`sda_nq`).
    // Start requests - which occur only during the Bus Idle condition, so the transceiver is
    // inactive - must lower SDA to prompt the Active Controller. This is done through `sreq_sda_i`,
    // driven from i3c_targ_start_req, which gets wired-ANDed onto the bus drive value below.
    // Both the resulting Start condition and the Active Controller starting to clock SCL in
    // response cause the transceiver to become active, but it has no knowledge of the data that is
    // supposed to go onto the bus due to the CDC delay. Therefore, i3c_targ_start_req must drive
    // the first three address bits through `sreq_sda_i`, and the transceiver must output all-ones.
    // On the fourth bit, data has eventually arrived (through `trx_areq_i`), handover occurs, and
    // the roles switch (transceiver drives, i3c_targ_start_req must output logic high).
    //
    // TODO: Handover not yet implemented: `arb_starting` is a single pulse at the first SCL falling
    // edge, which is before `trx_avalid_i` can have crossed the CDC, and the transceiver's
    // contribution to the wired-AND is not forced high while it is not driving (`sda_nq` still
    // holds data from the previous frame).
    assign bus_drv_o.sda = ((sda_out_ptog ^ sda_out_ntog) ? sda_pq[0][8] : sda_nq[0][8])
                           & sreq_sda_i;

    // Use a separate pair of toggle bits for the enables because these _do_ need to change on
    // a half-cycle basis for SDR transmission, because of the T-bit in SDR Read transfers.
    logic sda_en_ptog;
    always_ff @(posedge scl_i or negedge rst_ni) begin
      if (!rst_ni) sda_en_ptog <= 1'b0;
      else if (!transmitting) sda_en_ptog <= 1'b0;
      else sda_en_ptog <= !sda_en_ptog;
    end
    logic sda_en_ntog;
    always_ff @(posedge scl_ni or negedge rst_ni) begin
      if (!rst_ni) sda_en_ntog  <= 1'b0;
      else if (!transmitting) sda_en_ntog <= 1'b0;
      else sda_en_ntog <= sda_en_ptog;
    end

    // Driver enables must switch too.
    // Counterpart of the wired-AND for SDA above: the two enables are OR'ed. Since a '1' is
    // indistinguishable from released on an open-drain bus, the enable windows of the two owners
    // must overlap rather than abut, such that SDA is never let go part-way through a bit.
    assign bus_drv_o.sda_pp_en =  (sda_en_ptog ^ sda_en_ntog) ? sda_pp_en_pq : sda_pp_en_nq;
    assign bus_drv_o.sda_od_en = ((sda_en_ptog ^ sda_en_ntog) ? sda_od_en_pq : sda_od_en_nq)
                                 | sreq_sda_od_en_i;  // Start request and addressing.
  end else begin : gen_no_tokens
    // This approach just uses the clock state directly, but introduces a combinational path
    // from SCL to SDA. Comments about `sreq_sda_i` and `sreq_sda_od_en_i` from the UseTokens branch
    // above still apply.
    assign bus_drv_o.sda = (scl_i ? sda_pq[0][8] : sda_nq[0][8]) & sreq_sda_i;

    // Driver enables must switch too.
    assign bus_drv_o.sda_pp_en =  scl_i ? sda_pp_en_pq : sda_pp_en_nq;
    assign bus_drv_o.sda_od_en = (scl_i ? sda_od_en_pq : sda_od_en_nq) | sreq_sda_od_en_i;
  end

  // Detection of conflict on the SDA line; this detects arbitration loss or a driver conflict with
  // the Active Controller.
  wire sda_driven = (bus_drv_o.sda_pp_en | bus_drv_o.sda_od_en);
  assign sda_diff = &{sda_driven, sda_i != bus_drv_o.sda[0]};

  // -------------------------- Arbitration Requests from Target core ------------------------------

  // TODO: No support for arbitration requests at present (port does not exist).
  //assign trx_agnt_o = 1'b0;

  // -------------------------------- Response to Target core --------------------------------------

  // TODO: Request/response interface is incomplete at present; just capture the received word here
  // for checking.
  for (genvar t = 0; t < NumTargets; t++) begin : gen_dready
    assign trx_dready_o[t] = tx_starting & (t == trans.targ_id) & !ccc_command;
  end
  assign trx_ctready_o = tx_starting & ccc_command;
  // Signalling mode, such that the core knows how much of the presented read data each
  // `trx_dready_o`/`trx_ctready_o` pulse is valid (two bytes for HDR-DDR, one byte for SDR).
  assign ddr_mode_o = ddr_mode;

  // We want to warn the FSM as soon as possible that prefetched read data is required.
  // TODO: Rename, and give more thought to the introduction of a suitable state encoding.
  wire rxd_sr = &{ccc_state_q == CCC_SegAddr, direct_get(trans.cmd), bit_idx == BitW'(8)};

  // Under-construction response to the FSM logic.
  i3c_targ_trx_rxd_t rxd;
  always_comb begin
    rxd = '0;
    // TODO: It seems quite likely that we want a simplified encoding here:
    //  setup, sr, segaddr, segread, segwrite.
    rxd.sr        = (ccc_state_q == CCC_SegAddr) & direct_get(trans.cmd);
    rxd.ccc_state = ccc_state_q;
    rxd.ccc_idx   = ccc_idx_q;
    rxd.rnw       = trans.rnw;
    // TODO: At the point of trying to capture the phase/segment address/targ_id/targ_set
    // `trans` has not yet been updated in CCC_SegAddr state. Sort out timing here...perhaps
    // everything needs to be captured during the final bit, re-timing now-stale data if necessary?
    if (ccc_state_q == CCC_SegAddr) begin
      rxd.targ_id   = targ_id;
      rxd.targ_set  = targ_set;
      rxd.addr      = addr_recvd;
      rxd.is_group  = is_group;
    end else begin
      rxd.targ_id   = trans.targ_id;
      rxd.targ_set  = trans.targ_set;
      rxd.addr      = trans.addr;
      rxd.is_group  = trans.is_group;
    end
    case (state_q)
      State_RxCmdDDR,
      State_RxDataDDR: begin
        rxd.wdata = ddr_payload;
        rxd.dtype = (state_q == State_RxDataDDR) ? I3CDType_DataWord : I3CDType_CommandWord;
      end
      State_RxCRCDDR: rxd.dtype = I3CDType_CRCWord;
      default: begin
        rxd.wdata[7:0] = sdr_payload;
        rxd.dtype = I3CDType_SDRBytes;
      end
    endcase
  end

  // TODO: Very much need to nail down what gets passed to the FSM. Perhaps the FSM should have
  // the responsibility, we just tell it the extra state above.
  wire rxd_reqd = |{state_q inside {State_RxSDR, State_RxCmdDDR, State_RxDataDDR, State_RxCRCDDR},
                    (ccc_state_q == CCC_SegAddr &&  // Address required.
                     state_q inside {State_ArbCont, State_ArbCede, State_AckAddr}),
                    rxd_sr};

  always_ff @(posedge scl_ni or negedge rst_ni) begin
    if (!rst_ni) begin
      trx_rtoggle_o <= 1'b0;
      trx_rxd_o     <= '0;
    end else begin
      if (rxd_reqd) begin
        // Capture the SDR or HDR-DDR data without the parity bits, because this information is
        // required in the final SCL cycle in preparation for sending read data.
        if (penult_bit | rxd_sr) begin
          // Note that we cannot check the parity or CRC-5 at this point.
          trx_rxd_o <= rxd;
        end
        // Present the information, if appropriate.
        if ((last_bit & !enthdr_det) | rxd_sr) begin
          trx_rtoggle_o     <= !trx_rtoggle_o;
          trx_rxd_o.status  <= (parity_error_sdr | parity_error_ddr) ? TTIRxStatus_ErrParity :
                               (crc5_error ? TTIRxStatus_ErrCRC : TTIRxStatus_OK);
        end
      end
    end
  end

endmodule
