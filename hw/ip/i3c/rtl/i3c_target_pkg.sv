// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Target-side definitions.

package i3c_target_pkg;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
  import i3c_tti_pkg::*;

  // The Target must also respond to the I3C Broadcast Address (7'h7e), and an additional encoding
  // is used within the Target transceiver logic to indicate the address did not match anything.
  localparam int unsigned TargIDW = $clog2(MaxTargets + 2);
  localparam bit [TargIDW-1:0] TargIDNoMatch   = TargIDW'(MaxTargets);
  localparam bit [TargIDW-1:0] TargIDBroadcast = TargIDW'(MaxTargets+1);
  // We need a small number of states here for tracking transfer framing, in particular CCCs
  // in HDR-DDR mode if/when completed (HCI v1.2 does not support their use).
  // Most of the CCC handling is kept within the Target Core logic, operating on the IP block.
  typedef enum logic [2:0] {
    CCC_Idle,
    CCC_Setup,    // Set up, including CCC and optional Defining Byte.
    CCC_SegAddr,  // Address at the start of a Read/Write Segment.
    CCC_SegData,
    CCC_Private   // Private Read/Write transfer, not CCC framing.
  } i3c_targ_ccc_state_e;

  // Target device description.
  // - this is used by both the Target core and the Target transceiver logic.
  typedef struct packed {
    // Is this target enabled? Disabled targets do not participate in address assignment.
    logic        en;
    // Does this target have a valid address of any form?
    logic        addr_valid;
    // Is it a dynamic address?
    logic        addr_dynamic;
    // Address of the Target itself.
    logic  [6:0] addr;

    // Data Transfer Early Termination Configuration.
    logic        en_write_nack;  // May NACK Write commands?
    logic        en_write_term;  // May perform Early Termination of Write transfers?
    logic        en_early_crc;   // Include CRC Word after Early Termination of Read transfers?
  } i3c_targ_dev_t;

  // Additional information about the Target that is required by the Target core logic in order to
  // process Command Command Codes.
  typedef struct packed {
    logic [47:0] pid;  // Provisional ID.
    logic  [7:0] dcr;  // Device Characteristics Register.
    logic  [7:0] bcr;  // Bus Characteristics Register.
  } i3c_targ_info_t;

  // Group address description.
  typedef struct packed {
    logic            [6:0] addr;
    // Subset of Virtual Targets presently subscribed to this group address.
    // - if this is zero, the group description is invalid and shall be ignored.
    logic [MaxTargets-1:0] targets;
    // The VT set in the register always has MaxTarget bits; being defensive, we treat this group
    // as valid iff a configured and present VT is subscribed.
    logic                  valid;
  } i3c_grp_addr_t;

  // Set maximum read, write, IBI length.
  typedef struct packed {
    logic                  setmwl;   // As opposed to SETMRL.
    logic                  setibi;   // Optional, SETMRL only.
    logic [MaxTargets-1:0] targets;  // Set of affected Targets.
    logic           [15:0] mwrl;     // Length for SETMW|RL.
    logic            [7:0] ibil;     // Optional max IBI payload length.
  } i3c_setml_t;

  // Enable/Disable Target-side IBI generation.
  typedef struct packed {
    logic [MaxTargets-1:0] enint;   // Regular In-Band Interrupts.
    logic [MaxTargets-1:0] disint;
    logic [MaxTargets-1:0] encr;    // Controller Role requests.
    logic [MaxTargets-1:0] discr;
    logic [MaxTargets-1:0] enhj;    // Hot-Join requests.
    logic [MaxTargets-1:0] dishj;
  } i3c_endis_event_t;

  // Description of a Target transceiver prefetch request.
  typedef struct packed {
    // Target being addressed.
    logic [TargIDW-1:0] targ_id;
    // Indicates whether `cmd` is a CCC value.
    logic               ccc;
    // Command code, including RnW as its MS bit for non-CCC prefetch requests,
    // or Direct-not-Broadcast as its MS bit for `cmd` values that denote Common Command Codes.
    logic         [7:0] cmd;
    // Signaling mode.
    logic               ddr_mode;
  } i3c_targ_trx_pre_t;

  // Description of transmit data for Private Read transfers.
  // - this must be presented up front for each supported target, allowing the transceiver to
  //   respond with sufficient speed to a Read command.
  typedef struct packed {
    // Read data (from the perspective of the Controller).
    logic        [8:0] rdata_nq;  // Odd-indexed bits of HDR-DDR word, or SDR byte.
    logic        [8:0] rdata_pq;  // Even-indexed bits; unused for SDR reads.
    logic        [1:0] rlast;     // 'Last byte' indication for each of the two bytes.
  } i3c_targ_trx_txd_t;

  // Description of transmit data for Direct Read CCCs.
  // - data for all Targets is carried as a single unit to simplify the CDC into the SCL domain.
  typedef struct packed {
    // Read data (from the perspective of the Controller).
    logic [MaxTargets-1:0][8:0] rdata_nq;  // Odd-indexed bits of HDR-DDR word, or SDR byte.
    logic [MaxTargets-1:0][8:0] rdata_pq;  // Even-indexed bits; unused for SDR reads.
    logic [MaxTargets-1:0][1:0] rlast;     // 'Last byte' indication for each of the two bytes.
    // TODO: Proposal for consideration:
    // - Signaling method; we need to employ Open Drain and arbitration for the 48-bit dynamic
    //   address...this will be supplied a number of units at a time, and we must retain arb_lost
    //   from one unit to the next.
  } i3c_targ_trx_txc_t;

  // Description of an Arbitration request to the Target transceiver.
  // - In-Band Interrupt or Controller-Role Request.
  typedef struct packed {
    logic [TargIDW-1:0] targ_id;   // ID of Target. TODO: Required only if _trx signals back to core
    logic         [6:0] addr;      // Address to be used in arbitration request.
    logic               ibi;       // 1 for true IBI, 0 for Controller-Role request.
    logic         [8:0] rdata_nq;  // SDR word for transmission, including 'last' bit.
  } i3c_targ_trx_arb_t;

  // Type of data unit/event to be actioned by the Target core.
  typedef enum logic [2:0] {
    // Control flow.
    TDType_RepStart,
    // HDR-DDR Words.
    TDType_CommandWord,
    TDType_DataWord,
    TDType_CRCWord,
    // SDR signaling.
    TDType_SDRBytes
  } i3c_targ_dtype_e;

  // Description of a Target transceiver response.
  // TODO: This is a bit heavy-handed; obvious application for a union.
  // - We need to signal:
  //   - outcome of transfer
  //   - received data and the size/type of the data? Perhaps we only forward the Data Words
  //     and not any framing? Need to forward command code, of course.
  //   - state during data rteception (CCC setup, CCC segment addr, CCC segment data, priv data)
  //   - target(s) involved; surely we don't need single target ID, target set and address?
  //
  typedef struct packed {
    // TODO: Fold 'sr' into 'dtype'...see above.
    logic                   sr;  // Repeated Start has precedence over the other fields.
    i3c_targ_ccc_state_e    ccc_state;
    logic             [3:0] ccc_idx;
    logic                   rnw;
    // Response type.
    i3c_tti_rx_status_e     status;
    // Data type.
    i3c_targ_dtype_e        dtype;
    logic     [TargIDW-1:0] targ_id;
    logic  [MaxTargets-1:0] targ_set;
    logic             [6:0] addr;
    logic                   is_group;
    // Write data (from the perspective of the Controller).
    logic      [TargDW-1:0] wdata;
  } i3c_targ_trx_rxd_t;

endpackage
