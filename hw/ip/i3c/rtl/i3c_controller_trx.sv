// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I3C Controller transceiver.
//
// - SCL-driving I3C transmitter/receiver.

module i3c_controller_trx
  import i3c_controller_pkg::*;
  import i3c_io_pkg::*;
  import i3c_pkg::*;
#(
  parameter int unsigned ClkFreq = 50_000_000,
  parameter bit          PrimaryCtrl = 1'b1,
  // Number of SDA lanes; must be one presently since HDR-BT mode not supported.
  parameter int unsigned NumSDALanes = 1,
  parameter int unsigned DataWidth = 32,
  parameter int unsigned TmCycW = 10,
  parameter bit          HalfCycleScl = 1'b0  // Include support for extending SCL high?
) (
  input                         clk_i,
  input                         rst_ni,

  // Control inputs.
  input                         enable_i,  // Clock-gating, never used to pause the logic.
  input                         sw_reset_i,
  input                         hotjoin_ctrl_i,

  // Blocked device addresses.
  // TODO: Implement this debug/safety functionality.
  input                   [6:0] addr_blocked_i[NumBlocked],
  input                   [6:0] mask_blocked_i[NumBlocked],

  // Start request to the Controller core, on behalf of I3C Target(s).
  output                        trx_sreq_o,

  // Request from the Controller core.
  input                         trx_dvalid_i,
  output                        trx_dready_o,
  input  i3c_ctrl_trx_req_t     trx_dreq_i,

  // Arbitration requests to the Controller core.
  output                        trx_avalid_o,
  output i3c_ctrl_trx_arb_t     trx_arb_o,
  input                         trx_aready_i,

  // Read data to the Controller core.
  output                        trx_rdvalid_o,
  output i3c_ctrl_trx_rdata_t   trx_rdata_o,

  // Response to the Controller core.
  output                        trx_rvalid_o,
  input                         trx_rready_i,
  output i3c_ctrl_trx_rsp_t     trx_rsp_o,

  // Configured target- and transfer-invariant timing parameters.
  input            [TmCycW-1:0] tcas_d2_i,
  input            [TmCycW-1:0] tcbp_d2_i,

  // Start request signaling from Targets.
  // - SDA input that has been synchronized to the IP clock.
  input                         sreq_sda_i,

  // I3C I/O signaling.
  input       [NumSDALanes-1:0] sda_i,
  output i3c_ctrl_bus_drv_t     bus_drv_o,

  // Pull-up enables.
  output                        scl_pu_en_o,
  output                        sda_pu_en_o,

  // Debug status information.
  output logic            [5:0] bcl_tfr_status_o
);

  import i3c_consts_pkg::*;
  import i3c_timing_pkg::*;

  localparam int unsigned Log2DW = $clog2(DataWidth);

  // Fault injection for testing Targets.
  // TODO: Decide whether to keep this functionality.
  localparam bit FIParity = 1'b0;
  localparam bit FICRC5   = 1'b0;

  // Return the length in bits of the given unit type, minus 1 for counting down.
  function automatic bit [Log2DW-1:0] unitlen_bits(i3c_ctrl_req_e req);
    case (req)
      CReqType_CommandWord,
      CReqType_DataWord:   return Log2DW'(19);
      // CRC Words are 12 bits including the final setup bit ('1') for HDR Restart/Exit.
      CReqType_CRCWord:    return Log2DW'(11);
      CReqType_SDRBytes,
      CReqType_DynAddr:    return Log2DW'(8);

      CReqType_Address,
      CReqType_ArbAddr:    return Log2DW'(7);

      CReqType_ArbDAA:     return Log2DW'(7);  // No ACK bit in DAA reads.
      // Other requests may count down cycles during their operation, and perhaps consist of
      // multiple phases, but they are treated as single-bit units.
      // - CReqType_AckNack.
      default:             return Log2DW'(0);
    endcase
  endfunction

  // Current SDA output, when driving.
  logic sda_q;
  // Data buffer.
  logic [DataWidth-1:0] buf_q;

  // SCL/SCL_PP_En are driven directly from bits of the state variable to eliminate glitches that
  // could otherwise result from any combinational logic.
  localparam int unsigned ST_SCL_PP_EN = 1;
  localparam int unsigned ST_SCL       = 0;

  typedef enum logic [6:0] {
    State_Reset           = 7'b00000_0_1,

    // --- Inactive bus state; SCL high and SDA high ---
    State_Idle            = 7'b00000_1_1,

    // --- Basic SDR signaling ---
    State_Stalling        = 7'b00000_1_0,  // Controller can stall the bus for a while with SCL low.
    State_PreStart        = 7'b00001_1_1,
    State_Start           = 7'b00001_1_0,
    State_Stop            = 7'b00010_1_1,
    State_PreStop         = 7'b00010_1_0,
    State_RepStart        = 7'b00011_1_0,
    State_RepStartHiD     = 7'b00100_1_0,
    State_RepStartHiC     = 7'b00011_1_1,
    State_RepStartLoD     = 7'b00100_1_1,

    // --- Address phases ---
    //
    // Arbitrable     - Following Start in SDR mode.
    //                - ENTDAA read data; SDA undriven by Controller.
    State_ArbClkLoSetupD  = 7'b00101_1_0,
    State_ArbClkHiHoldD   = 7'b00101_1_1,
    State_ArbClkHiIdle    = 7'b00110_1_1,
    State_ArbClkLoIdle    = 7'b00110_1_0,

    // Non-arbitrable - Following Repeated Start; Controller push-pull signaling except ACK.
    State_AddrClkLoSetupD = 7'b00111_1_0,
    State_AddrClkHiHoldD  = 7'b01101_1_1,
    State_AddrClkHiSetupD = 7'b01110_1_1,
    State_AddrClkLoHoldD  = 7'b01000_1_0,

    // Collect Ack/Nack response from the Target(s) or Group.
    State_WAckClkLoSetupD = 7'b10010_1_0,

    // --- Data Transmission ---

    // SCK low->high transition.
    State_ClkLoSetupD     = 7'b01001_1_0,
    State_ClkHiHoldD      = 7'b00111_1_1,
    // SCK high->low transition.
    State_ClkHiSetupD     = 7'b01000_1_1,
    State_ClkLoHoldD      = 7'b01010_1_0,

    // --- Data reception ---

    // SCK low->high transition
    State_ClkLoAwaitD     = 7'b01011_1_0,
    State_ClkHiSampleD    = 7'b01001_1_1,
    // SCK high->low transition
    State_ClkHiAwaitD     = 7'b01010_1_1,
    State_ClkLoSampleD    = 7'b01100_1_0,

    // --- HDR Exit, HDR Restart, Target Reset ---
    State_PatternHiD      = 7'b01101_1_0,
    State_PatternLoD      = 7'b01110_1_0,

    // --- Error states ---
    //
    // Consume any further requests until our response is acknowledged by the Controller core.
    State_ClkLoResponse   = 7'b10000_1_0,
    State_ClkHiResponse   = 7'b01100_1_1,

    // --- Direct-driving of pins under software control ---
    State_ClkLoDirDrv     = 7'b00000_0_0,
    State_ClkHiDirDrv     = 7'b00001_0_1,
    State_ClkLoPPDirDrv   = 7'b10001_1_0,
    State_ClkHiPPDirDrv   = 7'b10000_1_1
  } state_e;

  // Transceiver state.
  state_e state_q, state_d;

  // A note on terminology:
  //
  // - A single request may transfer up to a full DWORD from/to the Controller core.
  // - A unit transferred over the I3C bus carries either 8 bits (I2C or SDR) or 16 bits (HDR-DDR)
  //   of data payload, with additional bits for framing and/or parity.
  // - Within a single request there may therefore be one or more `units`.
  // - Each unit is transferred by running the clock (SCL) through multiple phases.
  // - Each phase may consume multiple cycles of the IP clock, since it is at least 4 times the
  //   signaling frequency of SCL and must be slowed by extending the `SCL high` and/or `SCL low`
  //   phases in a transfer- and target-dependent fashion.

  logic [TmCycW-1:0] cnt;
  // Final cycle of the current phase/state; potentially about to perform a state transition.
  wire phase_end = ~|cnt;
  // Final cycle of a bit being transferred.
  logic bit_done;
  // Final cycle of the current unit.
  logic unit_end;

  // Index of bit within the current transmission unit, counting down to 0 because the MSB is sent
  // is first.
  logic [Log2DW-1:0] bit_idx;
  // Is the current output bit part of the payload, i.e. it contributes to parity and/or CRC-5?
  logic tx_data_bit_q;
  // Captured request properties.
  typedef struct packed {
    i3c_ctrl_req_e      req;   // Type of request.
    i3c_ctrl_timing_t   tm;    // Timing parameters for this request.
    logic               rx;    // Reception, not transmission.
    logic  [Log2DW-4:0] ilen;  // Initial request length (number of bytes minus 1).
    logic  [Log2DW-4:0] len;   // Read/write length (number of units minus 1).
    logic               last;  // Last request of transfer?
  } req_t;
  req_t req_q;

  // Derived timing parameters.
  // - the register configuration specifies tCAS/2-1 and tCBP/2-1 (in IP clock cycles).
  // - tCAS/2 and tCBP/2 are the push-pull timings used for Repeated Start signaling.
  // - the corresponding open drain timings used for regular Start and Stop are tCAS and tCBP;
  //   we derive those here, being sure to set the LSB since the values are '-1' adjusted
  //   for counting down to zero.
  wire [TmCycW-1:0] tcas = {tcas_d2_i[TmCycW-2:0], 1'b1};
  wire [TmCycW-1:0] tcbp = {tcbp_d2_i[TmCycW-2:0], 1'b1};

  logic last_bit;      // Final bit _within this unit_.
  logic penult_bit;    // Penultimate bit _within this _unit_.
  logic tx_data_bit;   // The _next_ bit is a data bit within the transmitted word.
  logic rx_data_bit;   // The current bit is a data bit within the received word.
  logic last_req_bit;  // Final bit within the final unit of this request.

  // Different reasons for terminating a request.
  logic req_ok_early, req_err_early;
  logic req_ending_early;
  // TODO: Error and Abort handling incomplete.
  wire  req_aborted = 1'b0;
  wire  req_failed = 1'b0;
  assign req_err_early = req_failed | req_aborted;
  assign req_ending_early = req_ok_early | req_err_early;

  // Properties of the next unit; these depend upon whether we're continuing with the current
  // request. These shall only be used when `unit_starting` is asserted.
  struct {
    i3c_ctrl_req_e req;
    logic          ddr;
    logic          rx;
  } next_unit;

  // Starting a new request?
  wire req_starting = trx_dvalid_i & trx_dready_o;
  // Ending the current request?
  // - this can be successful completion, successful early termination, error or abort.
  wire req_ending = |{last_req_bit & bit_done, req_ending_early};
  // Continuation within an ongoing request?
  wire req_continuing = unit_end & |req_q.len;
  // Starting to transmit an HDR-DDR word? (Command Word, Data Word or CRC Word.)
  wire ddr_tx_starting = req_starting & next_unit.ddr & !trx_dreq_i.rx;
  // Start a Command Word?
  wire cmd_starting = req_starting & (trx_dreq_i.req == CReqType_CommandWord);
  // About to issue Target Reset signaling?
  wire targ_resetting = (trx_dreq_i.req == CReqType_TargetReset);
  // Starting a new unit?
  wire unit_starting = req_starting | req_continuing;
  always_comb begin
    next_unit.req = req_starting ? trx_dreq_i.req : req_q.req;
    next_unit.rx  = req_starting ? trx_dreq_i.rx  : req_q.rx;
    next_unit.ddr = next_unit.req inside {CReqType_CommandWord, CReqType_DataWord,
                                          CReqType_CRCWord};
  end

  // Does the current request demand Double Data Rate (DDR) signaling?
  wire ddr_mode = (req_q.req inside {CReqType_CommandWord, CReqType_DataWord, CReqType_CRCWord});
  // CRC words are shorter than other HDR-DDR words.
  wire ddr_crc  = (req_q.req == CReqType_CRCWord);  // Transferring a CRC word.
  wire ddr_crcn = ddr_mode & !ddr_crc;              // Transferring a non-CRC HDR-DDR word.

  // SDR Reading/Writing, for the in-progress request but not when it is starting.
  wire sdr_read  = (req_q.req == CReqType_SDRBytes) &  req_q.rx;
  wire sdr_write = (req_q.req == CReqType_SDRBytes) & !req_q.rx;

  // Each party (Controller plus Target) gets to vote on whether to continue an SDR Read Transfer.
  //
  // We need to sample the T-bit of an SDR read _before_ the SCL rising edge so that we know
  // when to drive it low (Figure 87 vs. Figure 85).
  wire sdr_tbit_sample = &{sdr_read, penult_bit, state_q == State_ClkLoSampleD, phase_end};

  // Desired state of T-bit for an SDR Read operation.
  // - we drive the T-bit low if this is the last byte of SDR read data that we want to accept.
  wire sdr_tbit_intent = |{req_q.len, ~req_q.last};

  // Whether the Target wishes to continue the SDR Read Transfer ('1') or terminate it ('0').
  logic sdr_tbit_drive_q;
  logic sdr_tbit_targ_q;
  wire sdr_tbit_drive = &{sdr_read, last_bit, phase_end,
                          |{!sdr_tbit_targ_q & (state_q == State_ClkLoAwaitD),
                            !sdr_tbit_intent & (state_q == State_ClkHiSampleD)}} | sdr_tbit_drive_q;

  wire sdr_read_ending = &{sdr_read, last_bit, phase_end, state_q == State_ClkLoSampleD,
                           sdr_tbit_drive_q};
  // TODO: This is presently the only case of early termination that we handle, but there will be
  // others such as HDR-DDR since a request can accommodate two Data Words.
  assign req_ok_early = sdr_read_ending;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sdr_tbit_targ_q   <= 1'b1;
      sdr_tbit_drive_q  <= 1'b0;
    end else if (sw_reset_i) begin
      sdr_tbit_targ_q   <= 1'b1;
      sdr_tbit_drive_q  <= 1'b0;
    end else if (enable_i) begin
      if (sdr_read_ending) begin
        sdr_tbit_targ_q   <= 1'b1;
        sdr_tbit_drive_q  <= 1'b0;
      end else begin
        // Capture the T-bit from the Target, indicating whether it wishes to continue or terminate
        // the SDR Read transfer.
        if (sdr_tbit_sample) sdr_tbit_targ_q <= sda_i[0];
        sdr_tbit_drive_q <= sdr_tbit_drive;
      end
    end
  end

  // Transmission of SDR/HDR-DDR data bits.
  wire transmitting = (state_q inside {State_ClkLoSetupD, State_ClkHiHoldD,
                                       State_ClkHiSetupD, State_ClkLoHoldD});

  // Addresses are entirely data, the Ack/Nack bit is handled as a separate request, unlike the
  // T bit of SDR signaling.
  wire addr_req = (req_q.req inside {CReqType_ArbDAA, CReqType_ArbAddr, CReqType_Address});

  // Decide whether the _next_ bit is a data bit, requiring a shift of the data buffer `buf_q`.
  always_comb begin
    tx_data_bit = req_starting ? !next_unit.ddr :  // SDR Write starts with data, HDR-DDR does not.
                      ddr_mode ? (ddr_crc ? (bit_idx >= Log2DW'('h1) && bit_idx < Log2DW'('h0b))  :
                                            (bit_idx >= Log2DW'('h3) && bit_idx < Log2DW'('h13))) :
                                 // SDR Write traffic or Address header.
                                 (addr_req || bit_idx != Log2DW'('h1));

    rx_data_bit = req_starting ? !next_unit.ddr : // SDR Read starts with data, HDR-DDR does not.
                      ddr_mode ? (ddr_crc ? (bit_idx < Log2DW'('h0a)) :
                                            (bit_idx >= Log2DW'('h2) && bit_idx < Log2DW'('h12))) :
                                 // SDR Read traffic or Address header.
                                 (addr_req || |bit_idx);
  end

  wire tx_advance = |{state_q == State_ClkHiHoldD && ddr_mode,
                      state_q == State_ClkLoHoldD,
                      state_q == State_Start,
                      state_q == State_RepStartLoD,
                      state_q == State_AddrClkLoHoldD,
                      state_q == State_ArbClkLoIdle && req_q.req == CReqType_ArbAddr,
                      state_q == State_ArbClkLoIdle && last_req_bit
                     } & phase_end;
  wire tx_load    = req_starting & !trx_dreq_i.rx;
  wire tx_shift   = tx_advance & tx_data_bit;
  wire rx_advance = |{state_q == State_ArbClkHiHoldD,
                      state_q == State_ClkLoAwaitD,
                      state_q == State_ClkHiAwaitD && ddr_mode} & phase_end;
  wire rx_shift   = rx_advance & rx_data_bit;

  wire buf_shift  = tx_shift | rx_shift;

  // Direct-driving of pins under software control?
  // - not normal I3C traffic, but useful for testing purposes and for bus recovery.
  wire direct_drive = state_q inside {State_ClkLoDirDrv,   State_ClkHiDirDrv,
                                      State_ClkLoPPDirDrv, State_ClkHiPPDirDrv};
  // Possible state transition.
  wire advance = enable_i & phase_end;

  // Pattern counter (HDR Restart, HDR Exit and Target Reset signaling).
  wire patt_advance = (state_q == State_PatternHiD) & phase_end;

  logic starting, pre_stop, stop;
  // Indications of preantepenultimate, prepenultimate, penultimate and the last bit;
  // these are useful for both the addressing phase and the reception of HDR-DDR words.
  wire   preant_bit = (bit_idx == Log2DW'('d3));
  wire   prepen_bit = (bit_idx == Log2DW'('d2));
  assign penult_bit = (bit_idx == Log2DW'('d1));
  // Final bit within _this unit_?
  assign last_bit = ~|bit_idx;
  // Final bit of the final unit within this request?
  assign last_req_bit = (last_bit & ~|req_q.len) | req_ending_early;

  // Preamble (HDR-DDR only) and parity (SDR/HDR-DDR) bit indicators.
  // Note that these signals are asserted in the preceding bit intervals, to ensure that 'sda_d'
  // is ready.

  // We're starting an HDR-DDR word; we can ascertain this from the requested transfer mode.
  wire hdr_pre1_bit = unit_starting & next_unit.ddr;
  wire hdr_pre0_bit = (bit_idx == Log2DW'('h13));  // All other units contain fewer bits.
  wire hdr_para_bit = (req_q.req == CReqType_CommandWord) & preant_bit;
  wire hdr_par1_bit = ddr_crcn & prepen_bit;
  wire hdr_par0_bit = ddr_crcn & penult_bit;
  wire sdr_par_bit  = (req_q.req == CReqType_SDRBytes) & penult_bit;

  // Target Start request received.
  assign trx_sreq_o = &{advance, state_q == State_Idle, !sreq_sda_i & !trx_dvalid_i};

  // Any request from the Controller core whilst we're Idle leads to Start signaling.
  assign starting   = &{advance, state_q == State_Idle, trx_dvalid_i};
  // We must lower SDA for the second part of HDR Restart/SDR Repeated Start signaling.
  assign restarting = &{advance, state_q inside {State_RepStart, State_RepStartHiD}};
  // We must lower SDA before we can raise it for STOP signaling.
  assign pre_stop   = &{advance, state_q == State_PreStop};
  // STOP signaling; SDA raised but SCL still driven low.
  assign stop       = &{advance, state_q == State_Stop};
  // Issuing Target Reset signaling?
  wire targ_reset   = (req_q.req == CReqType_TargetReset);

  // Generation of HDR Exit/Restart signaling.
  wire [2:0] hdr_patt_cnt = bit_idx[2:0];  // HDR pattern and data Tx/Rx never occur simultaneously.
  wire gen_hdr_patt   = (trx_dreq_i.req == CReqType_HDRExit ||
                         trx_dreq_i.req == CReqType_HDRRestart) & trx_dvalid_i;
  wire leave_hdr_exit = (req_q.req == CReqType_HDRExit)    & ~|hdr_patt_cnt;
  wire leave_hdr_sr   = (req_q.req == CReqType_HDRRestart) & ~|hdr_patt_cnt;
  wire leave_targ_rst = targ_reset & ~|hdr_patt_cnt;

  // Has an error condition occurred within this transfer?
  // TODO: We shall perhaps need to make this sticky.
  logic raise_error;

  // Single data bit used in parity and CRC-5 calculation.
  wire parcrc_bit = (transmitting ? sda_q : buf_q[0]);

  // Parity calculated on transmitted/received data.
  // - HDR-DDR collects two independent parity bits, one on the odd bits and one on the even bits.
  logic       parity_sdr_tx;
  logic [1:0] parity_q;  // {PA1, PA0}
  logic [1:0] parity_d;
  logic [1:0] upd_parity;
  logic       init_parity;
  // Does the current bit contribute to the parity?
  // - for SDR or HDR-DDR transmission all data bits contribute.
  // - for HDR-DDR reception we include PA1 and PA0, with the result that the parity should be zero.
  // - for SDR reception there is no parity checking.
  wire parity_contrib = transmitting ? (bit_done & tx_data_bit_q)
                                     : (ddr_mode & rx_advance & bit_idx < Log2DW'('h12));
  // - SDR employs odd parity across all 8 data bits, but must also include the current bit,
  //   and `parity_q` has not yet been updated to reflect that; use `parity_d`.
  assign parity_sdr_tx = ^parity_d;
  // Does the current bit contribute to the parity calculations?
  assign upd_parity[1] = (parity_contrib &  bit_idx[0]) & !init_parity;
  assign upd_parity[0] = (parity_contrib & !bit_idx[0]) & !init_parity;
  // Parity must be reinitialized at the start of each transmitted data unit, as well as being
  // updated with the new data.
  assign init_parity = unit_starting;
  wire  [1:0] parity_mod = {parity_q[1] & ~init_parity, parity_q[0] | init_parity};
  assign parity_d = parity_mod ^ ({2{parcrc_bit}} & upd_parity);  // Updating `q` is conditional.

  // CRC-5 calculated on transmitted/received data; operating on a single bit at a time.
  logic [4:0] crc5_q;
  logic [4:0] crc5_d;
  logic init_crc, upd_crc;
  wire next_crc0 = crc5_q[4] ^ parcrc_bit;
  assign crc5_d = init_crc ? '1 : {crc5_q[3:2], next_crc0 ^ crc5_q[1], crc5_q[0], next_crc0};
  // Update CRC-5 with this bit?
  assign upd_crc = &{ddr_mode, bit_done, tx_data_bit_q, req_q.req != CReqType_CRCWord};
  // Initialize the CRC-5 when we first encounter a Command Word; this cannot be coincident with
  // updating the CRC.
  assign init_crc = cmd_starting;

  // Do the calculated parity and CRC-5 values match against the received values?
  wire parity_check = &{(req_q.req == CReqType_DataWord), (state_q == State_ClkLoSampleD),
                        last_bit, req_q.rx};
  wire parity_error = parity_check & |parity_q;

  wire crc5_match = (crc5_q == buf_q[4:0]);
  wire crc5_check = &{(req_q.req == CReqType_CRCWord), req_q.rx, penult_bit};
  wire crc5_error = crc5_check & !crc5_match;

  // Length of the current data unit, in bits.
  logic [Log2DW-1:0] d_bits_m1;
  assign d_bits_m1 = unitlen_bits(trx_dreq_i.req);

  // Is a bit transfer completed?
  // - this includes non-data bits.
  always_comb begin
    bit_done = 1'b0;
    case (state_q)
      // Twice per SCL cycle for HDR-DDR mode.
      State_ClkHiHoldD,
      State_ClkHiSampleD: bit_done = phase_end & ddr_mode;
      // Bit transfer completed, in any mode.
      State_Start,
      State_Stop,
      State_Stalling,
      State_RepStartLoD,
      State_ArbClkLoIdle,
      State_AddrClkLoHoldD,
      State_ClkLoHoldD,
      State_ClkLoSampleD,
      State_ClkLoDirDrv,
      State_ClkHiDirDrv,
      State_ClkLoPPDirDrv,
      State_ClkHiPPDirDrv: bit_done = phase_end;
      default: begin end
    endcase
  end

  // Transition at the end of a unit within a request.
  assign unit_end = &{bit_done, last_bit};

  // Accept a new request upon completion of the current unit.
  assign trx_dready_o = |{starting,
                          req_ending,
                          state_q == State_PatternLoD & leave_hdr_sr,
                          state_q == State_PatternHiD & leave_hdr_exit};

  // Interpret the new command.
  i3c_ddr_cmd_word_t dreq_cmd;
  assign dreq_cmd = i3c_ddr_cmd_word_t'(trx_dreq_i.wdata);

  // Properties of the current, in-progress request.
  // - `state_q` retains the information on whether this is a valid request; there is no need to
  //   invalidate `req_q` in response to, for example, `sw_reset_i` assertion.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) req_q <= '0;
    else if (enable_i) begin
      if (req_starting) begin
        // Retain the details of the current request.
        req_q.req  <= trx_dreq_i.req;
        // To support odd-length transfers in HDR-DDR mode we receive a byte count and convert here.
        req_q.ilen <= trx_dreq_i.len;              // Initial request length.
        req_q.len  <= trx_dreq_i.len >> ddr_mode;  // Updated during transfer, now in units.
        req_q.last <= trx_dreq_i.last;
        req_q.rx   <= trx_dreq_i.rx;
        // Timing parameters for this request; target- and mode-dependent.
        req_q.tm   <= trx_dreq_i.tm;
      end else if (unit_end) begin
        // Repetition within the current request; one or more units left.
        // Note: do not underflow because the number of outstanding units is returned in our
        // response, alongside the error status.
        req_q.len  <= req_q.len - |req_q.len;
      end
    end
  end

  logic arb_lost;
  // Take over responsibility for Actively holding SDA low (ACK).
  wire sdr_ack_handoff = &{(state_q == State_WAckClkLoSetupD), last_bit, phase_end};

  // PRE1 for transmission; Table 79 - PRE[1:0] = 01 for Command/CRC, 11 for Data.
  wire tx_pre1 = ((req_starting ? trx_dreq_i.req : req_q.req) == CReqType_DataWord);

  // SDA normally acquires the value of the data buffer MSB when it advances, but to keep the
  // line free of glitches it must be driven directly from a flop. It therefore assumes the
  // correct state for (S)tart and sto(P) signaling, as well as receiving injected preamble, parity
  // and CRC-5 bits.
  logic sda_d;
  always_comb begin
    sda_d = sda_q;
    // Set SDA to the appropriate state for (S)tart and sto(P) signaling.
    // Ditto for the HDR Restart/Exit and Target Reset patterns.
    if (&{state_q == State_PatternLoD, phase_end, !leave_hdr_exit}) begin
      sda_d = 1'b1;
    end else if (state_q == State_PatternHiD && phase_end) sda_d = leave_targ_rst;
    else if (|{starting, restarting, pre_stop, stop}) sda_d = restarting | stop;
    else if (state_q == State_RepStartHiC) sda_d = 1'b0;
    else if (sdr_ack_handoff) sda_d = sda_i[0];
    else if (sdr_tbit_drive) sda_d = 1'b0;  // We only ever drive it low; open drain signaling.
    else if (tx_advance) begin
      // When emitting SDR write data or DDR-HDR words, we need to inject the calculated parity.
      // Preamble and Parity bits are not part of the data supplied by the controller.
      unique casez ({hdr_pre1_bit, hdr_pre0_bit, hdr_para_bit,
                     hdr_par1_bit, hdr_par0_bit, sdr_par_bit})
        6'b1?????: sda_d = tx_pre1;       // PRE1, indicates Data Word rather than Command/CRC.
        6'b01????: sda_d = 1'b1;          // PRE0, always driven high, but Target may pull it low.
        6'b001???: sda_d = ~parity_q[0];  // PARA, parity adjustment.
        6'b0001??: sda_d = parity_q[1];   // PAR1
        6'b00001?: sda_d = parity_q[0];   // PAR0
        6'b000001: sda_d = parity_sdr_tx;
        default: begin
          if (ddr_crc) begin
            case (bit_idx)
              // Inject the CRC-5 result into the transmitted CRC word at the appropriate position.
              'h6: sda_d = crc5_q[4];
              'h5: sda_d = crc5_q[3];
              'h4: sda_d = crc5_q[2];
              'h3: sda_d = crc5_q[1];
              'h2: sda_d = crc5_q[0];
              default: sda_d = buf_q[DataWidth-1];
            endcase
          end else begin
            sda_d = tx_load ? trx_dreq_i.wdata[DataWidth-1] : buf_q[DataWidth-1];
          end
        end
      endcase
    end else if (tx_load) sda_d = trx_dreq_i.wdata[DataWidth-1];
  end

  // Data to be parallel-loaded into the buffer.
  logic [DataWidth-1:0] buf_d;
  always_comb begin : gen_buf_data
    buf_d = buf_q;
    case ({tx_load, trx_dreq_i.req == CReqType_ArbAddr})
      // Loading data into a normal transmission-only phase.
      2'b10: buf_d[DataWidth-1:1] = trx_dreq_i.wdata[DataWidth-2:0];
      // Loading data into an Arbitrable Address phase causes SDA to be sampled into `buf_q`,
      // as well as transmitting from it.
      2'b11: begin : load_arbaddr
        // Populate two bits within the buffer for each bit of the supplied `wdata` to accommodate
        // the fact that we are both transmitting and sampling, but at different times within the
        // bit time. The buffer will thus be shifted twice per bit.
        for (int unsigned b = 0; b < 8; b++) begin
          buf_d[DataWidth-2*b-1] = trx_dreq_i.wdata[DataWidth-2-b];
          buf_d[DataWidth-2*b-2] = trx_dreq_i.wdata[DataWidth-2-b];
        end
      end
      // Buffer shifting for transmission and/or reception.
      default: buf_d[DataWidth-1:1] = buf_q[DataWidth-2:0];
    endcase
    // SDA input value, for read data but also for arbitration phases.
    buf_d[0] = sda_i[0];
  end

  // Data buffering.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sda_q <= '1;
      buf_q <= '0;
    end else if (sw_reset_i) sda_q <= 1'b1;
    else if (enable_i) begin
      // Update SDA output.
      // - Starting an SDR byte transmission we must output the MSbit immediately; there is no
      //   preamble.
      sda_q <= sda_d;
      // Shift the transmit/receive buffer and sample the SDA input.
      // - Starting an HDR-DDR word must capture all of the data bits because this is just the
      //   data payload and we will introduce the preamble and parity bits.
      if (ddr_tx_starting) buf_q <= trx_dreq_i.wdata;
      else if (tx_load | buf_shift) buf_q <= buf_d;
    end
  end

  // There are two reasons for detecting a mismatch between the observed SDA state and the SDA
  // state that we are trying to achieve:
  // - Arbitrable Address Headers; a Target may have won the arbitration.
  // - Contention on the SDA line, which we need to detect in order to invoke recovery procedures.
  logic sda_mismatch;

  // Next state transition upon completion of a request.
  state_e state_next_req;
  always_comb begin
    // These states are persistent; `state_next_req` is always used when `phase_end` is asserted.
    if (direct_drive) begin
      state_next_req = state_q;
    end else begin
      // The default next state, in the event of not receiving a request, shall be:
      // - Idle if SCL is high (normally this should only be entered for an inactive bus).
      // - Stalling if SCL is low.
      state_next_req = state_q[ST_SCL] ? State_Idle : State_Stalling;
    end

    // Handle the receive of a new request.
    if (trx_dvalid_i) begin
      case (trx_dreq_i.req)
        // SDR bus state signaling.
        // - (S)tart and sto(P) signaling rely upon the bus being in a defined state before SDA
        //   transitions; the `Pre` states establish these preconditions.
        CReqType_SDRStart:    state_next_req = State_PreStart;
        CReqType_SDRStop:     state_next_req = State_PreStop;
        CReqType_SDRRepStart: state_next_req = State_RepStart;
        // Arbitrable Address Header (after SDR Start, and ENTDAA read data).
        CReqType_ArbAddr,
        CReqType_ArbDAA:      state_next_req = State_ArbClkLoSetupD;
        // Non-Arbitrable Address Header (after SDR Rep Start, and ENTDAA DA assigment).
        CReqType_DynAddr,
        CReqType_Address:     state_next_req = State_AddrClkLoSetupD;
        // ACK/NACK handling is essentially the same signaling as the Arbitrable Address Header.
        CReqType_AckNack:     state_next_req = trx_dreq_i.rx ? State_WAckClkLoSetupD  // Receive.
                                                             : State_AddrClkLoSetupD; // Send.
        // SDR and HDR signaling.
        CReqType_SDRBytes,
        CReqType_CommandWord,
        CReqType_DataWord,
        CReqType_CRCWord:     state_next_req = trx_dreq_i.rx ? State_ClkLoAwaitD   // Reception.
                                                             : State_ClkLoSetupD;  // Transmission.
        // HDR Exit, HDR Restart and Target Reset signaling.
        // - these all involve a defined number of SDA falling edges with SCL held low.
        CReqType_HDRExit,
        CReqType_HDRRestart:  state_next_req = State_PatternLoD;
        CReqType_TargetReset: state_next_req = State_PatternHiD;
        CReqType_DirectDrive:
          // Open drain signaling takes precedence over push-pull driving,
          // TODO: ... but we have no open drain driver on SCL.
          casez (trx_dreq_i.wdata[27:24])
            4'b0001: state_next_req = State_ClkLoPPDirDrv;
            4'b0?1?: state_next_req = State_ClkLoDirDrv;
            4'b1001: state_next_req = State_ClkHiPPDirDrv;
            default: state_next_req = State_ClkHiDirDrv;
          endcase
        default: state_next_req = State_Idle;
      endcase
    end
  end

  // Transceiver state.
  always_comb begin
    state_d = state_q;
    case (state_q)
      // --- Idle, Stalling and Direct Driving persist until another request is received. ---
      State_Idle,
      State_Stalling,
      State_ClkLoDirDrv,
      State_ClkLoPPDirDrv,
      State_ClkHiDirDrv,
      State_ClkHiPPDirDrv:    state_d = state_next_req;
      // --- Activation after Reset ---
      State_Reset:            state_d = State_Idle;  // Enables SCL push-pull driver.
      // --- Reporting of Status/Error response to the Controller core ---
      State_ClkLoResponse:    state_d = trx_rready_i ? state_next_req : State_ClkLoResponse;
      State_ClkHiResponse:    state_d = trx_rready_i ? state_next_req : State_ClkHiResponse;
      // --- SDR START ---
      State_PreStart:         state_d = State_Start;
      State_Start:            state_d = targ_resetting ? State_PatternHiD : state_next_req;
      // --- Address Arbitration ---
      State_ArbClkLoSetupD:   state_d = State_ArbClkHiHoldD;
      State_ArbClkHiHoldD:    state_d = State_ArbClkHiIdle;
      State_ArbClkHiIdle:     state_d = State_ArbClkLoIdle;
      State_ArbClkLoIdle:     state_d = last_req_bit ? state_next_req : State_ArbClkLoSetupD;
      // --- Controller Ack/Nack response to Arbitrable Address Header ---
      State_WAckClkLoSetupD:  state_d = State_ArbClkHiHoldD;
      // --- Non-arbitrable Address ---
      State_AddrClkLoSetupD:  state_d = State_AddrClkHiHoldD;
      State_AddrClkHiHoldD:   state_d = State_AddrClkHiSetupD;
      State_AddrClkHiSetupD:  state_d = State_AddrClkLoHoldD;
      State_AddrClkLoHoldD:   state_d = last_req_bit ? state_next_req : State_AddrClkLoSetupD;
      // --- Data Transmission ---
      State_ClkLoSetupD:      state_d = State_ClkHiHoldD;
      State_ClkHiHoldD:       state_d = State_ClkHiSetupD;
      State_ClkHiSetupD:      state_d = State_ClkLoHoldD;
      State_ClkLoHoldD:       state_d = last_req_bit ? state_next_req : State_ClkLoSetupD;
      // --- Data Reception ---
      State_ClkLoAwaitD:      state_d = State_ClkHiSampleD;
      State_ClkHiSampleD:     state_d = State_ClkHiAwaitD;
      State_ClkHiAwaitD:      state_d = State_ClkLoSampleD;
      State_ClkLoSampleD:     state_d = last_req_bit ? state_next_req : State_ClkLoAwaitD;
      // --- HDR Exit, HDR Restart and Target Reset ---
      // TODO: The Controller must sit in this state for quite a while if the bus was idle,
      // monitoring SDA to ensure that nothing pulls it low (4.3.9.3).
      State_PatternHiD:       state_d = leave_targ_rst ? State_RepStart :
                                       (leave_hdr_sr   ? state_next_req : State_PatternLoD);
      State_PatternLoD:       state_d = leave_hdr_exit ? state_next_req : State_PatternHiD;
      // --- SDR Repeated Start ---
      State_RepStart:         state_d = State_RepStartHiD;
      State_RepStartHiD:      state_d = State_RepStartHiC;
      State_RepStartHiC:      state_d = State_RepStartLoD;
      State_RepStartLoD:      state_d = targ_reset ? State_Stop : state_next_req;
      // --- SDR STOP ---
      State_PreStop:          state_d = State_Stop;

      // The default case handles State_Stop as well as invalid states.
      default:                state_d = State_Idle;
    endcase
  end

  // Default state duration in clock cycles (2 cycles at 50MHz), minus 1 because downcounting.
  localparam int unsigned ClkKhz = i3c_timing_pkg::ceil_div(ClkFreq, 1000);
  localparam int unsigned DefTmCyc = i3c_timing_pkg::ceil_div(40 * ClkKhz, 1_000_000) - 1;
  // Duration of the next state, in clock cycles.
  // - most of these timings are supplied with the request because they are target- and mode-
  //   dependent.
  logic [TmCycW-1:0] tm_cycles;
  always_comb begin
    if (unit_starting) begin
      // When transitioning to a new unit/request, the next state is difficult to predict from the
      // current state alone, so we use the request type.
      case (next_unit.req)
        CReqType_SDRStart: tm_cycles = tcas;
        CReqType_SDRStop:  tm_cycles = tcbp;
        CReqType_ArbAddr,
        CReqType_AckNack,
        CReqType_Address,
        CReqType_SDRBytes,
        CReqType_CommandWord,
        CReqType_DataWord,
        CReqType_CRCWord:  tm_cycles = trx_dreq_i.tm.tcls;
        default:           tm_cycles = DefTmCyc;
      endcase
    end else begin
      // We can use the current state here because the next state, and thus its duration, are very
      // predictable.
      case (state_q)
        State_Idle:            tm_cycles = tcas;
        State_Start:           tm_cycles = targ_resetting ? DefTmCyc : trx_dreq_i.tm.tcls;
        // SCL low, setup/await data...SCL high next.
        State_ArbClkLoSetupD,
        State_AddrClkLoSetupD,
        State_ClkLoSetupD,
        State_ClkLoAwaitD:     tm_cycles = req_q.tm.tchh;
        // SCL high, hold/sample data...SCL remains high.
        State_ArbClkHiHoldD,
        State_AddrClkHiHoldD,
        State_ClkHiHoldD,
        State_ClkHiSampleD:    tm_cycles = req_q.tm.tchs;
        // SCL high, setup/await data...SCL low next.
        State_ArbClkHiIdle,
        State_AddrClkHiSetupD,
        State_ClkHiSetupD,
        State_ClkHiAwaitD:     tm_cycles = req_q.tm.tclh;
        // SCL low...SCL remains low.
        State_ArbClkLoIdle,
        State_AddrClkLoHoldD,
        State_ClkLoHoldD,
        State_ClkLoSampleD:    tm_cycles = req_q.tm.tcls;
        // Direct-driving of pins under software control; collect new state from FSM on each cycle.
        State_ClkLoDirDrv,
        State_ClkHiDirDrv,
        State_ClkLoPPDirDrv,
        State_ClkHiPPDirDrv:   tm_cycles = '0;
        // HDR Exit/Restart signaling requires 2 cycles per state at 50MHz.
        // - covered by the default timing.
        default:               tm_cycles = DefTmCyc;
      endcase
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      crc5_q        <= '1;
      parity_q      <= 2'b01;
      cnt           <= '0;
      state_q       <= State_Reset;
      bit_idx       <= '1;
      tx_data_bit_q <= 1'b0;
    end else if (sw_reset_i) begin
      crc5_q        <= '1;
      parity_q      <= 2'b01;
      cnt           <= '0;
      state_q       <= State_Reset;
      bit_idx       <= '1;
      tx_data_bit_q <= 1'b0;
    end else if (enable_i) begin
      if (req_starting) begin
        // Behavior specific to the new data unit.
        case (trx_dreq_i.req)
          CReqType_HDRRestart:  bit_idx <= Log2DW'(2);  // Re-purposing the `bit_idx` counter for...
          CReqType_HDRExit:     bit_idx <= Log2DW'(4);  // ...counting SDA negative edges.
          CReqType_TargetReset: bit_idx <= Log2DW'(7);
          CReqType_DirectDrive,                         // Collect new drive state for every bit.
          CReqType_AckNack:     bit_idx <= Log2DW'(0);  // Single ACK/NACK bit.
          // Normal transmission/reception.
          default:              bit_idx <= d_bits_m1;
        endcase
      end else if (patt_advance) begin
        bit_idx <= bit_idx - 'b1;
      end else if (bit_done) begin
        // Counting of bits within data unit/repetition of data unit.
        bit_idx <= last_req_bit ? Log2DW'(0) :
                      (last_bit ? unitlen_bits(req_q.req) : (bit_idx - 'b1));
      end

      // Decide whether the current output bit contributes to parity and CRC-5 calculations;
      // the first bit of the transfer unit contributes for SDR but not for HDR-DDR words.
      if (unit_starting) tx_data_bit_q <= !next_unit.ddr;
      else if (bit_done) tx_data_bit_q <= tx_data_bit;

      // Conditionally update CRC-5 and parity.
      if (init_crc | upd_crc) crc5_q <= crc5_d ^ {3'b0, FICRC5, 1'b0};
      if (init_parity | upd_parity[1]) parity_q[1] <= parity_d[1];
      if (init_parity | upd_parity[0]) parity_q[0] <= parity_d[0] ^ (FIParity & parity_d[0]);

      if (phase_end) begin
        // Advance the signaling state machine.
        state_q   <= state_d;
        cnt       <= tm_cycles;
      end else begin
        cnt       <= cnt - 'b1;
      end
    end
  end

  // Tracking of arbitration loss
  // - targets and other controllers may interject when we are transmitting an 'Arbitrable Address.'
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      arb_lost  <= 1'b0;
    end else if (enable_i) begin
      case (state_q)
        // Arbitration verdict is sticky throughout the address arbitration;
        // - as we transmit the arbitrable address we lose its value, but the comparison of
        //   received address cf transmitted is done bit-serially.
        State_ArbClkLoSetupD,
        State_ArbClkHiIdle,
        State_ArbClkLoIdle:  arb_lost <= arb_lost;
        // Update after SCL rising edge.
        State_ArbClkHiHoldD: arb_lost <= arb_lost | sda_mismatch;
        default:             arb_lost <= 1'b0;
      endcase
    end
  end

  // New state of the SDA driver enables.
  // - uses the above three functions to set up the driver enables for the next clock cycle.
  drv_state_t sda_drv_q, sda_drv_d;
  always_comb begin
    sda_drv_d = sda_drv_q;
    if (unit_starting) begin
      // Set up the appropriate driver state for the next request.
      case (next_unit.req)
        // SDR Start, stoP and Repeated Start.
        CReqType_SDRStart:    sda_drv_d = open_drain();
        CReqType_SDRRepStart,
        CReqType_SDRStop:     sda_drv_d = push_pull();
        // Arbitrable Address Header.
        CReqType_ArbAddr:     sda_drv_d = open_drain();
        CReqType_ArbDAA:      sda_drv_d = pull_up();
        // Ack/Nack following Address Header.
        // - if we lost the arbitration we are the recipient of an IBI, CRR or Hot-Join request,
        //   so we must resume driving to send the Ack/Nack bit.
        CReqType_AckNack:     sda_drv_d = next_unit.rx ? pull_up() : open_drain();
        // Assigning Dynamic Address.
        CReqType_DynAddr:     sda_drv_d = open_drain();
        // Push-pull transmission.
        CReqType_TargetReset,
        CReqType_Address,
        CReqType_HDRExit,
        CReqType_HDRRestart,
        CReqType_CommandWord: sda_drv_d = push_pull();
        // Transmission and reception in push-pull mode.
        CReqType_DataWord,
        CReqType_CRCWord,
        CReqType_SDRBytes:    sda_drv_d = next_unit.rx ? disconnect() : push_pull();
        // Direct drive of pin state under software control.
        CReqType_DirectDrive: begin
          // Open drain signaling takes precedence over push-pull driving, being safer.
          sda_drv_d = trx_dreq_i.wdata[DataWidth-3] ? open_drain() :
                     (trx_dreq_i.wdata[DataWidth-4] ? push_pull()  :
                     (trx_dreq_i.wdata[DataWidth-2] ? pull_up()    : disconnect()));
        end
        // The following also covers reception of push-pull transmissions.
        default:              sda_drv_d = disconnect();  // Play safe.
      endcase
    end else if (phase_end) begin
      // TODO: References to `state_next_req` should be disappearing from here.
      case (state_q)
        State_Reset: sda_drv_d = disconnect();
        // Leave the bus inactive with pull-up enabled until starting a transaction.
        State_Idle:  sda_drv_d = starting ? open_drain() : pull_up();

        // Address arbitration following a START employs open drain signaling, but the address
        // phase following a Repeated START in SDR mode employs push-pull signaling because
        // arbitration shall not occur.
        //
        // Note: Presently we do not try to optimize the driving of non-initial bits in Arbitrable
        // Address Header intervals, although this could be an optional configuration option.
        State_ArbClkLoSetupD: begin
          if (req_q.req == CReqType_AckNack && req_q.rx) begin
            if (arb_lost) begin
              // Handoff the ACK signaling to the Target.
              sda_drv_d = open_drain();
            end else begin
              // Take over responsibility for Actively holding SDA low (ACK).
              sda_drv_d = sda_i ? sda_drv_q : push_pull();
            end
          end
        end
        State_ArbClkHiIdle: begin
        end
        State_ArbClkLoIdle: begin
          //if (last_req_bit) begin
          //  // TODO: For ENTDAA we must continue reading..
          //  if (state_next_req != State_ArbClkLoSetupD) begin
          //    // Transitioning to SDR or I2C signaling _iff_ we have not lost arbitration.
          //    if (!trx_dreq_i.rx & !arb_lost) begin  // Transmitting?
          //      sda_drv_d = push_pull();
          //    end else sda_drv_d = disconnect();
          //  end
          //end else
          if (arb_lost | last_req_bit) begin
            // We've lost arbitration, so we do not drive out the remainder of the address header.
            sda_drv_d = pull_up();
          end else begin
            // With the Virtual Open Drain implementation, the driver enables change in a data bit-
            // dependent fashion, so we need to update them here.
            sda_drv_d = open_drain();
          end
        end

        State_AddrClkLoHoldD: begin
          if (last_bit) begin
            // TODO: Temporary; check timing for ACK bit of non-Arb address, including the
            // dynamic address assignment phase of ENTDAA.
            sda_drv_d = pull_up();
          end
        end

        State_ClkLoAwaitD: begin
          // The Target has presented its vote on SDR Read termination (Figure 85).
          if (!sdr_tbit_targ_q) sda_drv_d = open_drain();
        end

        State_ClkHiSampleD: begin
          // If the Target opted to continue an SDR Read but we want to terminate it, we do so at
          // this later time (Figure 87).
          if (&{sdr_read, last_bit, !sdr_tbit_intent}) sda_drv_d = open_drain();
        end

        State_ClkHiAwaitD: begin
          if (sdr_read & penult_bit) begin
            // For the T-bit of an SDR Read transfer we enables the pull-ups, but we let the Target
            // have the first vote.
            sda_drv_d = pull_up();
          end
        end

        State_ClkLoSampleD: begin
          if (last_req_bit) begin
            sda_drv_d = (state_next_req != State_ClkLoAwaitD) ? push_pull() : disconnect();
          end
        end

        // End of Command Word transmission may signal the start of data reception.
        State_ClkLoHoldD: begin
          if (last_req_bit) begin
            sda_drv_d = (state_next_req != State_ClkLoAwaitD) ? push_pull() : pull_up();
          end
        end

        State_Stop: sda_drv_d = pull_up();
        State_PatternHiD: if (leave_hdr_sr) sda_drv_d = pull_up();

        State_RepStartLoD: begin
          if (!targ_reset) begin
            if (state_next_req == State_AddrClkLoSetupD) sda_drv_d = push_pull();
            else sda_drv_d = pull_up();
          end
        end

        // These states do not change the state of the driver enables and must be listed
        // explicitly.
        State_PreStart,
        State_Start,
        State_PreStop,
        State_AddrClkLoSetupD,
        State_AddrClkHiHoldD,
        State_AddrClkHiSetupD,
        State_ArbClkHiHoldD,
        State_WAckClkLoSetupD,
        State_ClkLoSetupD,
        State_ClkHiHoldD,
        State_ClkHiSetupD,
        State_ClkLoAwaitD,
        State_ClkHiSampleD,
        State_ClkHiAwaitD,
        State_PatternLoD,
        State_RepStart,
        State_RepStartHiD,
        State_RepStartHiC,
        State_ClkLoDirDrv,
        State_ClkHiDirDrv,
        State_ClkLoPPDirDrv,
        State_ClkHiPPDirDrv: begin end

        // Handle invalid states; relinquish everything but the pull-up.
        default: sda_drv_d = pull_up();
      endcase
    end
  end

  // Detection of conflict on SDA line; this detects arbitration loss or a driver conflict with the
  // target.
  logic sda_driven;
  // TODO: The action taken on a mismatch, if any, shall depend upon the state.
  assign sda_mismatch = &{sda_driven, sda_i != bus_drv_o.sda[0]};

  // Driver enables.
  //
  // Note: this is more complicated for Virtual Open Drain output because the final driver outputs
  //       depend upon the state of the SDA lane(s).
  drv_state_t sda_drv_mod;
  if (DrvSeparatedEn) begin : gen_sda_en_sep_drv
    assign sda_drv_mod  = sda_drv_d;
  end else begin : gen_sda_en_vod_drv
    always_comb begin
      sda_drv_mod = sda_drv_d;
      // When using Open Drain signaling we need to deassert driver enables for high SDA lanes.
      sda_drv_mod.en = sda_drv_d.en & ~(sda_drv_d.od_en ? sda_d : 'b0);
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // We must have no impact upon the bus post-reset until our role has been decided.
      sda_drv_q  <= disconnect();
      sda_driven <= 1'b0;
    end else if (sw_reset_i) begin
      sda_drv_q  <= disconnect();
      sda_driven <= 1'b0;
    end else if (enable_i) begin
      sda_drv_q  <= sda_drv_mod;  // Virtual Open Drain support needs to modify `sda_drv_d`.
      // We also need the unmodified driver enable to detect a mismatch on SDA.
      sda_driven <= sda_drv_d.pp_en | sda_drv_d.od_en;
    end else begin
      // Have no impact upon the bus whilst the Controller is disabled.
      sda_drv_q  <= disconnect();
      sda_driven <= 1'b0;
    end
  end

  // Signaling is simplified at present by not supporting HDR-BT mode.
  assign bus_drv_o.sda = sda_q;
  if (DrvSeparatedEn) begin : gen_sda_sep_en
    // Driver Style 1 with two separate driver enables for SDA.
    assign bus_drv_o.sda_pp_en = sda_drv_q.pp_en;
    assign bus_drv_o.sda_od_en = sda_drv_q.od_en;
  end else begin : gen_sda_vod_en
    // Driver Style 2 with a single SDA driver enable and Virtual Open Drain.
    assign bus_drv_o.sda_en = sda_drv_q.en;
  end

  if (HalfCycleScl) begin : gen_hc_scl
    // This modification to 'SCL high' offers support for a larger set of IP clock frequencies
    // without violating the timing requirements of the I3C specification for 'SCL high.'
    // The penalty, however, is that combinational logic is required on the critical SCL output.
    logic scl_n;
    always_ff @(negedge clk_i or negedge rst_ni) begin
      if (!rst_ni) scl_n <= 1'b1;
      else if (sw_reset_i) scl_n <= 1'b1;
      else if (enable_i) begin
        // Extend the SCL high interval only when enabled, but without impacting Start signaling.
        scl_n <= &{state_q[ST_SCL], req_q.tm.hcext, state_q != State_PreStart};
      end
    end

    assign bus_drv_o.scl = state_q[ST_SCL] | scl_n;
  end else begin : gen_pure_scl
    assign bus_drv_o.scl = state_q[ST_SCL];
  end
  assign bus_drv_o.scl_en = state_q[ST_SCL_PP_EN];

  // Driver pull-up enables.
  // - These need to be enabled whenever open drain signaling is employed by any party.
  assign scl_pu_en_o = 1'b0;
  assign sda_pu_en_o = sda_drv_q.pu_en;

  // Reporting of arbitration outcome.
  // - this must be fast because deciding whether to ACK/NACK an IBI or CRR request demands a
  //   look up within the Device Address Table. This is mitigated by cacheing or mirroring the
  //   relevant fields of the DAT.
  // - we leave the Controller core to detect any invalid I3C addresses.
  i3c_ctrl_trx_arb_t arb_q, arb_d;
  always_comb begin
    arb_d = '0;
    arb_d.arb_lost = arb_lost;
    // Transmission and reception occurred at different moments during arbitration,
    // so the valid SDA input samples occupy alternate bits of `buf_q.`
    for (int unsigned b = 0; b < 7; b++) arb_d.addr[b] = buf_q[2*b+1];
    // Grab the RnW bit (indicating IBI, CRR or HJ) as soon as we can, because it can take a while
    // to decide how to respond.
    arb_d.ibi = sda_i[0];
    // Ack/Nack from the Target/Group when the Controller has won arbitration.
    arb_d.nack = sda_i[0];
  end

  // Send the header information to the Controller as soon as the final bit (RnW) is available.
  // - the RnW bit is required because it differentiates IBI from CRR.
  // - there's also a rather awkward case where Controller and Target drive the same address
  //   (that of the Target), as described in 4.3.2.2.3.
  //
  // When the Controller wins arbitration we also post an update that indicates the 'Ack/Nack'
  // response of the addressed Target/Group.
  wire arb_send = &{req_q.req == CReqType_ArbAddr || (req_q.req == CReqType_AckNack && req_q.rx),
                    state_q == State_ArbClkHiHoldD, last_bit, phase_end};
  logic avalid_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      avalid_q  <= 1'b0;
      arb_q     <= '0;
    end else if (sw_reset_i) avalid_q <= 1'b0;
    else if (enable_i) begin
      if (arb_send | trx_aready_i) avalid_q <= arb_send & ~trx_aready_i;
      if (arb_send & !avalid_q) arb_q <= arb_d;
    end
  end
  assign trx_avalid_o = avalid_q;
  assign trx_arb_o    = arb_q;

  // Data units are aggregated into full DWORDs within `buf_q` where possible, before writing into
  // the message buffer. This continues until we have a full DWORD or the transfer is terminated.
  assign trx_rdvalid_o = &{state_q == State_ClkLoSampleD, phase_end, last_req_bit,
                           req_q.req != CReqType_CRCWord} |  // All received data except the CRC.
                         &{state_q == State_ArbClkLoIdle, req_q.req == CReqType_ArbDAA,
                           phase_end, last_req_bit} |
                         req_ending_early;

  // Calculate the number of units remaining, for sending with read data and in the response.
  // - note that for error conditions this count includes one invalid unit, shuffled into `buf_q`,
  //   because the logic completes the transfer of that unit before it can detect an error.
  wire [Log2DW-4:0] bytes_left = ddr_mode ? {req_q.len[Log2DW-5:0], 1'b0} : req_q.len;
  wire [Log2DW-3:0] bytes_done = {1'b0, req_q.ilen} + 'b1 - {1'b0, bytes_left};

  // Read data.
  always_comb begin
    trx_rdata_o = '0;
    // We need to indicate whether this is DDR data, because that affects the byte ordering.
    trx_rdata_o.ddr    = ddr_mode;
    trx_rdata_o.rdata  = buf_q;

    // For an early termination because of an error, the final unit shuffled into
    // the `buf_q` shall be complete, to aid with data swizzling, but dropped afterwards.
    trx_rdata_o.rlen   = bytes_done;  // Number of bytes read.
    trx_rdata_o.rlast  = req_q.last | req_ending_early;  // Last unit; no more requests, please.
    trx_rdata_o.rearly = req_ending_early;  // The core needs to know of early termination.
    trx_rdata_o.rerr   = req_err_early;     // If asserted, the core shall ignore the final unit.
  end

  // Is this a Transfer termination state?
  wire term_state = (state_q inside {State_Stop, State_RepStart}) ||  // SDR termination.
                    (state_q inside {State_ClkLoSampleD, State_ClkLoHoldD} &&
                     req_q.req == CReqType_CRCWord);  // HDR-DDR termination.

  // TODO: The timing of these error signals must be qualified.
  assign raise_error = |{parity_error, crc5_error};  // TODO: sda_mismatch, at times.

  // Transfer completion signaling.
  // - successful transfer completion (ErrStatus_OK).
  // - error indication, which may occur at almost any point within the transfer, e.g. SDA mismatch.
  assign trx_rvalid_o = &{term_state, phase_end, last_req_bit} | req_ending_early;
  always_comb begin
    trx_rsp_o = '0;
    // TODO: report SDA mismatch; `i3c_err_status_e` is too limited to carry everything that we
    // shall need to report to the Controller core.
    trx_rsp_o.err_status = parity_error ? ErrStatus_Parity :
                             crc5_error ? ErrStatus_CRC    : ErrStatus_OK;
    trx_rsp_o.wlen   = bytes_done;
    trx_rsp_o.wearly = req_ending_early;
    trx_rsp_o.werr   = req_err_early;
  end

  // Debug Extended Capability
  // - map our line-level state machine onto the HCI-specified state information.
  // - this mapping cannot be perfect due to implementation details but it's close.
  always_comb begin
    // TODO: The transmit/receive states require further qualifications, in particular to report
    // ENTDAA, SETDASA and IBI.
    case (state_q)
      State_ClkLoSetupD,
      State_ClkHiHoldD,
      State_ClkHiSetupD,
      State_ClkLoHoldD:
        bcl_tfr_status_o = ddr_mode ? BCLStatus_HDRDDRWrite :
                              (1'b0 ? BCLStatus_BcastWrite  :
                              (1'b0 ? BCLStatus_TargetWrite : BCLStatus_I3CSDRWrite));

      State_ClkLoAwaitD,
      State_ClkHiSampleD,
      State_ClkHiAwaitD,
      State_ClkLoSampleD:
        bcl_tfr_status_o = ddr_mode ? BCLStatus_HDRDDRRead :
                              (1'b0 ? BCLStatus_TargetRead : BCLStatus_I3CSDRRead);
      default: bcl_tfr_status_o = BCLStatus_Idle;
    endcase
  end

endmodule
