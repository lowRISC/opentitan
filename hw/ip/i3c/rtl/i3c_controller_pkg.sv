// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Controller-side structure definitions.

package i3c_controller_pkg;
  import i3c_consts_pkg::*;
  import i3c_pkg::*;

  // --- Requests to the transceiver logic ---

  // Description of a Controller transceiver request.
  typedef struct packed {
    // Data type.
    i3c_dtype_e         dtype;
    // Timing parameters, as appropriate for the target and mode.
    // - push-pull timing parameters.
    logic  [TmCycW-1:0] tcls;
    logic  [TmCycW-1:0] tchh;
    logic  [TmCycW-1:0] tchs;
    logic  [TmCycW-1:0] tclh;
    // - open drain timing parameters.
    logic  [TmCycW-1:0] todcls;
    logic  [TmCycW-1:0] todchh;
    logic  [TmCycW-1:0] todchs;
    logic  [TmCycW-1:0] todclh;
    // Reception, not transmission.
    logic               rx;
    // Write data.
    logic      [DW-1:0] wdata;
    // Transfer length, in data units.
    // - [0:1] inclusive for 1-2 HDR-DDR word(s).
    // - [0:3] inclusive for 1-4 SDR byte(s).
    logic  [Log2DW-4:0] len;
    // Last request of transfer?
    logic               last;
  } i3c_ctrl_trx_req_t;

  // Description of an arbitration request to the Controller core.
  // - In-Band Interrupt, Controller-Role or Hot-Join Request.
  typedef struct packed {
    logic        arb_lost;  // Arbitration was lost.
    logic  [6:0] addr;      // Address read from SDA input.
    logic        ibi;       // IBI, or RnW bit set.
    logic        nack;      // NACKed rather than ACKed?
  } i3c_ctrl_trx_arb_t;

  // --- Responses from the transceiver logic ---

  // Read Data channel from the Controller transceiver.
  typedef struct packed {
    // Indicates whether the data was retrieved in DDR mode.
    logic               ddr;
    // Response data.
    logic      [DW-1:0] rdata;
    logic  [Log2DW-3:0] rlen;  // Number of bytes outstanding, [0:4].
    // Last response of transfer?
    logic               rlast;
  } i3c_ctrl_trx_rdata_t;

  // Description of a Controller transceiver response.
  typedef struct packed {
    // Response type, indicating any error condition,
    // or successful completion of the following requests:
    // - I3CDType_CRCWord (tx or rx)
    // - I3CDType_SDRStop
    // - I3CDType_SDRRepStart
    i3c_err_status_e err_status;
  } i3c_ctrl_trx_rsp_t;

  // Properties of the current HCI Command Descriptor, and properties preserved from earlier
  // Command Descriptor(s) forming a single Common Command Code transfer.
  //
  // - Command Descriptors may operate together to form a single CCC operation.
  // - Address Assignment commands require iteration, to assign a number of dynamic addresses.
  typedef struct packed {
    // Command Descriptor available; command ready to be actioned.
    // Note: This does not imply that the Command Descriptor has been accepted as valid.
    logic                 available;
    // Was the most recent command terminated with Sr rather than P?
    logic                 rep_start;
    // Atomicity.
    logic                 atomic;
    // Number of repetitions remaining.
    // - each repetition is a phase within e.g. a Combo Transfer or Address Assignment command.
    logic   [CmdRepW-1:0] reps_left;
    // Current DAT index; this advances whilst executing Address Assignment commands.
    logic  [DATAddrW-1:0] dev_index;
    // Command Descriptors performing a series of RSTACT CCCs are to be followed by the Target Reset
    // Pattern if it is not interrupted by failure or timeout.
    logic                 rst_csect;  // HCI 6.15.1

    // TODO: Support for retrying the Command a number of times if a NACK occurs.
    //       Perhaps we hold the CCC, DefByte and DefByte validity here instead of the registers?
  } i3c_ctrl_cmd_state_t;

endpackage
