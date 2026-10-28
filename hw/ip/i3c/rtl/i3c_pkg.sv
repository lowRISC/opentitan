// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Top-level IP block definitions.

package i3c_pkg;
  import i3c_consts_pkg::*;
  import i3c_reg_pkg::*;

  // IP block version information.
  localparam logic [3:0] IPVersion  = 4'h1;
  localparam logic [3:0] IPRevision = 4'h0;

  // Default values for the Hardware Identification Extended Capability.
  // - these may be overridden by supplying parameter values when instantiating the IP top level.
  localparam int unsigned CompManufacturer = 32'h0;
  localparam int unsigned CompVersion      = 32'h0;
  localparam int unsigned CompType         = 32'h0;

  // Number of SDA lines; presently, because multi-lane modes are not supported, this must be 1.
  localparam int unsigned NumSDALanes = 1;

  // Number of entries in the HCI Device Address Table
  // (This determines the maximum number of targets that may be addressed simultaneously using the
  //  Host Controller Interface.)
  localparam int unsigned NumDATEntries = NumDATWords / 2;

  // Number of entries in the HCI Device Characteristics Table
  // (The maximum number of devices that may be allocated dynamic addresses in a single allocation
  //  sequence.)
  localparam int unsigned NumDCTEntries = NumDCTWords / 4;

  // Maximum number of entries in the Controller DAT Cache.
  // - cacheing In-Band Interrupt and Controller-Role Request configuration reduces the latency of
  //   the Controller's ACK/NACK response; otherwise the Controller would need to search the DAT.
  // - the present simple implementation requires that we have enough cache for all current DAT
  //   entries; TODO(#31304): ratify and simplify, or modify as required.
  localparam int unsigned DATCacheSize = NumDATEntries;

  // The number of Target(s) presented simultaneously on the I3C bus, including the Standby
  // Controller, is a per-instance parameter (`NumTargets`) of the IP block top level.
  // Every Target-indexed data type below is sized for `MaxTargets` so that none of
  // them depends on that parameter. An instance configured with fewer Targets ties off the
  // surplus slices, which synthesis then removes.

  // Maximum number of groups to which a Target may be added.
  localparam int unsigned NumGroups = 8;

  // Number of blocked addresses supported; this is a safeguard against I2C devices that may use
  // clock-stretching, but may also be of use diagnostically.
  localparam int unsigned NumBlocked = 2;

  // Logical width of the data path; in practice this is constrained by the HCI specification.
  localparam int unsigned DW = 32;
  localparam int unsigned Log2DW = $clog2(DW);

  // Maximum width of the data received by the Target-side logic; HDR-DDR words.
  localparam int unsigned TargDW  = 16;
  localparam int unsigned Log2TDW = $clog2(TargDW);

  // General Host Controller interrupts.
  typedef struct packed {
    // The order of these fields is important in connecting to the `i3c_intr` instance.
    logic sched_cmd_missed_tick;
    logic hc_err_cmd_seq_timeout;
    logic hc_warn_cmd_seq_stall;
    logic hc_seq_cancel;
    logic hc_internal_err;
  } i3c_hc_intr_t;

  // PIO (Programmed Input/Output) Interrupts.
  typedef struct packed {
    // The order of these fields is important in connecting to the `i3c_intr` instance.
    logic transfer_err;
    logic transfer_abort;
    logic resp_ready;
    logic cmd_queue_ready;
    logic ibi_status_thld;
    logic rx_thld;
    logic tx_thld;
  } i3c_pio_intr_t;

  // Secondary Controller Interrupts.
  typedef struct packed {
    // The order of these fields is important in connecting to the `i3c_intr` instance.
    logic ccc_fatal_rstdaa_err;
    logic ccc_unhandled_nack;
    logic ccc_param_modified;
    logic stby_cr_op_rstact;
    logic stby_cr_accept_err;
    logic stby_cr_accept_ok;
    logic stby_cr_accept_nacked;
    logic stby_cr_dyn_addr;
    logic crr_response;
    logic acr_handoff_err_m3;
    logic acr_handoff_err_fail;
    logic acr_handoff_ok_primed;
    logic acr_handoff_ok_remain;
  } i3c_stby_cr_intr_t;

  // TTI Interrupts.
  typedef struct packed {
    // The order of these fields is important in connecting to the `i3c_intr` instance.
    logic te;
    logic [MaxTargets-1:0] tx_desc_ready;
    logic [MaxTargets-1:0] tx_thld;
    logic async_evt_ovf;
    logic rx_buffer_ovf;
    logic rx_desc_ovf;
    logic transfer_err;
    logic transfer_abort;
    logic async_evt_ready;
    logic ibi_status_thld;
    logic rx_desc_ready;
  } i3c_targ_intr_t;

  // --- HDR-DDR structure descriptions ---

  typedef struct packed {
    logic        rnw;        // 1: Read, 0: Write.
    logic [14:8] cmd_code;   // Command code.
    logic  [7:1] targ_addr;  // Dynamic address of target.
    logic        para;       // Parity Adjustment.
  } i3c_ddr_cmd_word_t;

  // --- End of HDR-DDR structure descriptions ---

  // --- Interface to/from the Target Reset detector ---

  typedef struct packed {
    logic     activate;    // Request to activate/deactivate the detector.
    logic     deep_sleep;  // Entering 'Deepest Sleep.' Issue Wake Up signaling on Target Reset.
    logic     rst_periph;  // Reset Peripheral if Target Reset signaling detected.
    logic     rst_target;  // Reset Whole Target if Target Reset signaling detected.
  } i3c_rstdet_req_t;

  typedef struct packed {
    logic     active;        // Detector is active.
    logic     wake_up_det;   // Wake from Deep Sleep detected.
    logic     peri_rst_det;  // Peripheral Reset detected.
    logic     targ_rst_det;  // Whole Target Reset detected.
  } i3c_rstdet_rsp_t;

  // Default connectivity, when there is no Target Reset detector.
  parameter i3c_rstdet_req_t I3C_RSTDET_REQ_DEFAULT = '0;
  parameter i3c_rstdet_rsp_t I3C_RSTDET_RSP_DEFAULT = '0;

  // --- TL-UL interface to FIFOs/buffers ---

  // TL-UL windows.
  //
  // Each of these address regions requires the ability to stall accesses briefly, awaiting
  // arbitration for access to the message buffer.
  //
  // Note that none of them stalls indefinitely, e.g. awaiting the availability of data or free
  // space. This is considered a software error, and null data is returned for reads, with writes
  // being swallowed. An error bit will be set in the register interface for diagnostic purposes.
  // Additionally, reads typically will not stall, because of the prefetching within the message
  // buffer.
  typedef enum {
    TL_HCI   = 0,  // HCI Command Queue, Response Queue, Transfer Data Buffer and IBI Port.
    TL_TTI   = 1,  // TTI Tx, Rx and IBI Buffers and Desc Queues, and Async Event Queue.

    // Larger memory windows, consisting of more than one addressable word.
    TL_DAT   = 2,  // HCI Device Address Table.
    TL_DCT   = 3,  // HCI Device Characteristics Table.
    TL_SwBuf = 4,  // Direct SW access to the entire message buffer.

    // Number of TL-UL windows.
    TL_Count
  } tl_win_e;

  localparam int unsigned TLWordCnt = 1 + TL_TTI;

  // HCI ports.
  typedef enum {
    HCI_Command,
    HCI_Response,
    HCI_XferData,
    HCI_IBI,

    // Number of HCI ports.
    HCI_Count
  } hci_port_e;

  // TTI ports.
  typedef enum {
    TTI_RxDesc = 0,
    TTI_RxData,
    TTI_IBIDesc = 2,
    TTI_IBIData,
    TTI_AsyncEvt,
    TTI_Tx0Desc = 5,  // Target Tx Descriptor ports; must be contiguous.
    TTI_Tx1Desc,
    TTI_Tx2Desc,
    TTI_Tx3Desc,
    TTI_Tx0Data = 9,  // Target Tx Data ports; must be contiguous.
    TTI_Tx1Data,
    TTI_Tx2Data,
    TTI_Tx3Data,

    // Number of TTI ports.
    TTI_Count
  } tti_port_e;

  // --- Interface to the internal message buffer ---

  // Size of message buffer, in words.
  localparam int unsigned BufWords = 1024;

  // Number of address bits.
  localparam int unsigned BufAddrW = $clog2(BufWords);

  // The FIFO-related structures used with `i3c_buffer` are defined in `i3c_fifo_pkg`.

  // Width of an index into the Device Address Table, in bits.
  localparam int unsigned DATAddrW = $clog2(NumDATEntries);

  // Width of the maximum number of repetitions.
  // - maximum width is determined by the `dev_count` field in Address Assignment Commands.
  localparam int unsigned CmdRepW = 4;

  // --- Timing parameters ---

  localparam int unsigned TmCycW = 10;  // Width of cycle counter in Controller transceiver.

  // Indicates whether the given address is an 'Error Type TE0' address (4.3.8.1.1).
  // - these are single-bit deviations from the I3C Broadcast Address 7'h7e.
  function automatic logic te0_invalid_addr(logic [6:0] addr);
    return (addr inside {7'h7f, 7'h7c, 7'h7a, 7'h76, 7'h6e, 7'h5e, 7'h3e});
  endfunction

  // Check whether the given I3C address is invalid before attempting to drive it out into an
  // arbitrable address header.
  // TODO(#31035): Target-side logic checking using this function also needs to catch 7'h7e/R except
  // when handling ENTDAA (4.3.8.1.1).
  function automatic logic invalid_addr(logic [6:0] addr, logic target);
    // See Table 10.
    unique case (addr)
      7'h00:   return 1'b1;
      // 7'h01 permissible, for supporting Minimal Bus Point-to-Point Communication.
      7'h02:   return !target;  // Hot-Join requests permissible only from Targets.
      default: return te0_invalid_addr(addr);
    endcase
  endfunction

  // The use of some CCCs is absolutely prohibited in Command Descriptors (TCRI 6.2) because the
  // Host Controller issues them internally. (Note that some others are conditionally-blocked.)
  function automatic logic tcri_blocked_ccc(logic [7:0] ccc);
    unique case (ccc)
      ENTHDR0, ENTHDR1, ENTHDR2, ENTHDR3, ENTHDR4, ENTHDR5, ENTHDR6, ENTHDR7,
      GETACCCR: return 1'b1;
      default:  return 1'b0;
    endcase
  endfunction

  // Broadcast CCCs need to be treated differently, especially on the Target side.
  function automatic logic broadcast_ccc(logic [7:0] ccc);
    return !ccc[7];
  endfunction

  // Direct GET, as opposed to Direct Set or Broadcast CCC?
  function automatic logic direct_get(logic [7:0] ccc);
    return ccc[7] & (ccc inside {GETMWL, GETMRL, GETPID, GETBCR, GETDCR, GETSTATUS,
                                 GETACCCR, GETMXDS, GETCAPS, GETXTIME});
  endfunction

  // A small number of the CCCs have a Defining Byte, which precedes the write data in the event
  // of a Broadcast CCC.
  function automatic logic ccc_has_defb(logic [7:0] ccc);
    // Note that we need only be concerned with those CCCs that are supported by the Target;
    // the Target transceiver logic is responsible for rejecting or ignoring CCCs/DEFBs that are not
    // supported.
    return ccc inside {ENTTM, RSTACTB, GETSTATUS, ENDXFER, ENDXFERB, GETMXDS, GETCAPS, RSTACT};
  endfunction

  // Indicates whether the Target supports the given Direct Common Control Command.
  // - this is for use in deciding whether to ACK/NACK the Target/Group address, so it is not
  //   concerned with Broadcast CCCs.
  function automatic logic supported_direct_ccc(logic [7:0] ccc);
    return ccc inside {ENEC, DISEC, SETDASA, SETNEWDA, SETMWL, SETMRL, GETMWL, GETMRL, GETPID,
                       GETBCR, GETDCR, GETSTATUS, GETACCCR, ENDXFER, GETMXDS, GETCAPS, RSTACT,
                       SETGRPA, RSTGRPA};
  endfunction

endpackage
