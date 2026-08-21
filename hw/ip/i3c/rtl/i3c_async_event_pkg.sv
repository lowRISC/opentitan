// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Asynchronous Event constants and types; part of the TTI.
// - this is not part of a MIPI Alliance standard, it is bespoke to the OpenTitan I3C Target.

package i3c_async_event_pkg;
  import i3c_consts_pkg::*;
  import i3c_reg_pkg::*;
  import i3c_tti_pkg::*;

  // Asynchronous Event Types.
  typedef enum logic [3:0] {
    // These are in order of descending priority.
    AsyncEv_CCC        = 4'h0,  // Notifications of Common Command Code activity.
    AsyncEv_NotifyTx   = 4'h1,  // The outcome of a Transmission attempt.
    AsyncEv_NotifyIBI  = 4'h2,  // Notifications of the outcome of attempted In-Band Interrupts.
    AsyncEv_TxSuspend  = 4'h3,  // Transmission by Virtual Target(s) suspended.
    AsyncEv_IBISuspend = 4'h4,  // Transmission of In-Band Interrupts suspended.
    AsyncEv_BusEvents  = 4'h5,  // Describes any significant events occurring on the I3C bus.
    // Sentinel gives the number of event types.
    AsyncEv_Count
  } i3c_tti_async_event_e;

  // The I3C Bus Events reported via the Asynchronous Event Queue.
  typedef enum logic [3:0] {
    TTIBusEv_ReadNoSCL   = 4'h0,  // No change in SCL for > 150us during a Read Transfer.
    TTIBusEv_DeadBus     = 4'h1,  // No response to Start request when the bus was idle.
    TTIBusEv_Idle        = 4'h2,  // Bus Idle condition (> 200us with no activity).
    TTIBusEv_TargetRst   = 4'h3,  // Target Reset signal received.
    // TODO: For CCC failures perhaps we want the _ccc_t information in some form?
    TTIBusEv_ParityCCC   = 4'h4,  // CCC not actioned because of a parity error.
    TTIBusEv_ChksumCCC   = 4'h5,  // CCC not actioned because of a CRC5 mismatch.
    TTIBusEv_UnknownCCC  = 4'h6,  // Common Command Code not known or not supported.
    TTIBusEv_UnknownDEFB = 4'h7,  // Defining Byte not known or not supported, for a known CCC.

    // Sentinel gives the number of bus event types.
    TTIBusEv_Count
  } i3c_tti_bus_event_e;

  // CCC Notification reported as an Asynchronous Event.
  // - followed by addresses and write data
  typedef struct packed {
    i3c_tti_async_event_e code;         // Specifies the type of this descriptor.
    i3c_ccc_e             ccc;          // Command Command Code received.
    logic           [1:0] reserved;
    logic                 has_defb;     // Does this CCC have a Defining Byte?
    logic                 has_length;   // Does `data_length` specify a data length?
    logic           [7:0] defb;         // The Defining Byte, if relevant.
    logic           [7:0] data_length;  // Single byte of write data, or number of bytes.
  } i3c_tti_async_ccc_t;

  // Outcome of a transmission attempt, reported as an Asynchronous Event.
  typedef struct packed {
    i3c_tti_async_event_e code;        // Specifies the type of this descriptor.
    i3c_err_status_e      err_status;  // Outcome of the transmission attempt.
    logic    [3-Log2MT:0] reserved;
    logic    [Log2MT-1:0] targ_id;     // Identifies the Virtual Target.
    logic           [3:0] tid;         // Transaction ID from Tx Descriptor.
    logic          [15:0] data_left;   // The number of bytes remaining in the Tx Buffer.
  } i3c_tti_async_txd_res_t;

  // Outcome of an IBI transmission attempt, reported as an Asynchronous Event.
  typedef struct packed {
    i3c_tti_async_event_e code;        // Specifies the type of this descriptor.
    i3c_err_status_e      err_status;  // Outcome of the IBI transmission attempt.
    logic    [3-Log2MT:0] reserved;
    logic    [Log2MT-1:0] targ_id;     // Identifies the Virtual Target.
    logic           [3:0] tid;         // Transaction ID from IBI Status Descriptor.
    logic          [15:0] data_left;   // The number of bytes remaining in the IBI Data Buffer.
  } i3c_tti_async_ibi_res_t;

  // Suspension of transmission from a Virtual Target.
  typedef struct packed {
    i3c_tti_async_event_e   code;      // Specifies the type of this descriptor.
    logic  [MaxTargets-1:0] targets;   // The target(s) for which transmission has been suspended.
    logic [27-MaxTargets:0] reserved;
  } i3c_tti_async_txd_susp_t;

  // Suspension of IBI transmission.
  typedef struct packed {
    i3c_tti_async_event_e code;      // Specifies the type of this descriptor.
    logic          [27:0] reserved;
  } i3c_tti_async_ibi_susp_t;

  // Bus Event reported as an Asynchronous Event.
  typedef struct packed {
    i3c_tti_async_event_e      code;      // Specifies the type of this descriptor.
    logic  [AsyncEv_Count-1:0] evt;       // The Bus Event(s) observed.
    logic [27-AsyncEv_Count:0] reserved;
  } i3c_tti_async_busevt_t;

  // Asynchronous Event Descriptor; single DWORD.
  typedef union packed {
    i3c_tti_async_ccc_t      ccc;
    i3c_tti_async_txd_res_t  txdr;
    i3c_tti_async_ibi_res_t  ibir;
    i3c_tti_async_txd_susp_t txds;
    i3c_tti_async_ibi_susp_t ibis;
    i3c_tti_async_busevt_t   bus;
  } i3c_tti_async_event_t;

endpackage
