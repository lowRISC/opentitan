// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Target Transaction Interface.
//
// - this is not part of a MIPI Alliance standard, it is bespoke to the OpenTitan I3C Target.
// - see doc/tti.md for details.

package i3c_tti_pkg;
  import i3c_consts_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;

  // The descriptors are specified in terms of the Maximum Targets rather than the configured number
  // to aid with driver portability.
  localparam int unsigned Log2MT = $clog2(MaxTargets);

  // Outcome of a received transfer.
  typedef enum logic [2:0] {
    TTIRxStatus_OK = 3'h0,
    TTIRxStatus_ErrCRC,
    TTIRxStatus_ErrParity,
    TTIRxStatus_RxOverflow,
    TTIRxStatus_BusAborted
  } i3c_tti_rx_status_e;

  // Description of a Pending Read Notification; single DWORD.
  typedef struct packed {
    logic        notify;  // Must be 1 -> Pending Read Notification.
    logic  [4:0] lsbs;    // The LSBs of the Pending Read Notification MDB.
    logic  [1:0] len;     // Number of additional data bytes (0-3).
    logic [23:0] data;    // Additional data bytes.
  } i3c_tti_prn_t;

  // Description of data for a Controller-initiated Read Transfer; single DWORD.
  typedef struct packed {
    logic        notify;       // Must be 0 -> Read Transfer.
    logic        wroc;         // Write response even on successful completion.
    logic  [9:0] reserved;
    logic  [3:0] tid;          // Transaction ID.
    logic [15:0] data_length;  // Number of bytes to be transmitted.
  } i3c_tti_tx_t;

  // Transmission Descriptor; single DWORD.
  // - may be either a Read Transfer descriptor or a Pending Read Notification.
  typedef union packed {
    i3c_tti_prn_t prn;  // Pending Read Notification.
    i3c_tti_tx_t  tx;   // Transmission.
  } i3c_tti_tx_desc_t;

  // Reception Descriptor; single DWORD.
  // - describes a Write Transfer, as received from the Active Controller.
  typedef struct packed {
    logic                   start;        // Start of a Write Transfer?
    logic                   complete;     // Write Transfer complete?
    i3c_tti_rx_status_e     status;       // Result of the Write Transfer.
    logic  [MaxTargets-1:0] targets;      // Which Target(s) matched the address.
    logic             [6:0] address;      // I3C Address of the Write Transfer.
    logic                   is_group;     // Address is a Group, rather than a Target?
    logic                   reserved;     // Reserved for future use.
    logic            [13:0] data_length;  // Number of bytes received.
  } i3c_tti_rx_desc_t;

  // IBI Status Descriptor; single DWORD.
  typedef struct packed {
    logic                 wroc;         // Write Response even On successful Completion.
    logic   [10-Log2MT:0] reserved;     // Reserved for future use.
    logic    [Log2MT-1:0] targ_id;      // The Virtual Target sending the IBI/CRR/HotJoin.
    logic           [7:0] mdb;          // Mandatory Data Byte.
    logic           [3:0] tid;          // Transaction ID.
    logic           [7:0] data_length;  // Count of the additional payload bytes, if any.
  } i3c_tti_ibi_status_t;

endpackage
