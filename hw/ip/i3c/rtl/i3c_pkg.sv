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
  //   entries; TODO: ratify and simplify, or modify as required.
  localparam int unsigned DATCacheSize = NumDATEntries;

  // Number of Target(s) presented simultaneously on the I3C bus, including the Standby Controller.
  localparam int unsigned NumTargets = 2;
  localparam int unsigned Log2NT = $clog2(NumTargets);

  // Maximum number of groups to which a Target may be added.
  localparam int unsigned NumGroups = 8;

  // The Target must also respond to the I3C Broadcast Address (7'h7e), and an additional encoding
  // is used within the Target transceiver logic to indicate the address did not match anything.
  localparam int unsigned TargIDW = $clog2(NumTargets + 2);
  localparam bit [TargIDW-1:0] TargIDNoMatch   = TargIDW'(NumTargets);
  localparam bit [TargIDW-1:0] TargIDBroadcast = TargIDW'(NumTargets+1);

  // Number of blocked addresses supported; this is a safeguard against I2C devices that may use
  // clock-stretching, but may also be of use diagnostically.
  localparam int unsigned NumBlocked = 2;

  // Logical width of the data path; in practice this is constrained by the HCI specification.
  localparam int unsigned DW = 32;
  localparam int unsigned Log2DW = $clog2(DW);

  // Maximum width of the data received by the Target-side logic; HDR-DDR words.
  localparam int unsigned TargDW  = 16;
  localparam int unsigned Log2TDW = $clog2(TargDW);

  // --- HCI/TCRI structure descriptions ---

  // Full DAT Entry as per the HCI Specification (HCI 8.1).
  typedef struct packed {
    logic [63:59] reserved2;
    logic [58:51] autocmd_hdr_code;
    logic [50:48] autocmd_mode;
    logic [47:40] autocmd_value;
    logic [39:32] autocmd_mask;
    logic         device;
    logic [30:29] dev_nack_retry_cnt;
    logic [28:26] ring_id;
    logic [25:24] reserved1;
    logic [23:16] dynamic_address;
    logic         ts;
    logic         crr_reject;
    logic         ibi_reject;
    logic         ibi_payload;
    logic [11:7]  reserved0;
    logic [6:0]   static_address;
  } i3c_dat_entry_t;

  // Packed DAT Entry as stored internally; as above but without the reserved fields.
  typedef struct packed {
    logic [58:51] autocmd_hdr_code;
    logic [50:48] autocmd_mode;
    logic [47:40] autocmd_value;
    logic [39:32] autocmd_mask;
    logic         device;
    logic [30:29] dev_nack_retry_cnt;
    logic [28:26] ring_id;
    logic [23:16] dynamic_address;
    logic         ts;
    logic         crr_reject;
    logic         ibi_reject;
    logic         ibi_payload;
    logic [6:0]   static_address;
  } i3c_dat_mem_t;

  // Full DCT Entry as per the HCI Specification (HCI 8.2).
  typedef struct packed {
    logic [127:104] reserved2;
    logic [103:96]  dynamic_address;
    logic [95:80]   reserved1;
    logic [79:72]   bcr;
    logic [71:64]   dcr;
    logic [63:48]   reserved0;
    logic [47:32]   pid_lo;
    logic [31:0]    pid_hi;
  } i3c_dct_entry_t;

  // Packed DCT Entry as stored internally; as above but without the reserved fields.
  typedef struct packed {
    logic [103:96]  dynamic_address;
    logic [79:72]   bcr;
    logic [71:64]   dcr;
    logic [47:32]   pid_lo;
    logic [31:0]    pid_hi;
  } i3c_dct_mem_t;

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
    logic async_evt_ovl;
    logic rx_buffer_ovl;
    logic transfer_err;
    logic transfer_abort;
    logic async_evt_ready;
    logic ibi_status_thld;
    logic rx_desc_ready;
  } i3c_targ_intr_t;

  // Immediate Data Transfer Command. Format 1 (TCRI 7.1.2.1).
  // - many fields are present in all command types; annotated here.
  typedef struct packed {
    logic     [7:0] data_byte_4;
    logic     [7:0] data_byte_3;
    logic     [7:0] data_byte_2;
    logic     [7:0] data_byte_1;
    logic           toc;        // Terminate On Completion.
    logic           wroc;       // Write Response On Completion.
    logic           rnw;        // Direction (Read, not Write).
    i3c_xfer_mode_e mode;       // Mode and Speed.
    logic     [2:0] dtt;        // Data Transfer Type and byte count.
    logic     [1:0] reserved;
    logic     [4:0] dev_index;  // Index into DAT, to retrieve device/group properties.
    logic           cp;         // Command Present.
    i3c_ccc_e       cmd;        // Command, used for CCC or HDR Command Word, iff `cp` set.
    logic     [3:0] tid;        // Transaction ID.
    i3c_cmd_attr_e  cmd_attr;   // Command Attribute (specifies command type).
  } i3c_xfer_cmd_imm_t;

  // Regular Transfer Command. Format 1 (TCRI 7.1.2.2).
  typedef struct packed {
    logic    [15:0] data_length;
    logic     [7:0] reserved1;
    logic     [7:0] def_byte;        // Defining Byte, if used.
    logic           toc;
    logic           wroc;
    logic           rnw;
    i3c_xfer_mode_e mode;
    logic           dbp;             // Defining Byte Present.
    logic           short_read_err;  // Short Read is Error; fewer bytes not allowed.
    logic     [2:0] reserved;
    logic     [4:0] dev_index;
    logic           cp;
    i3c_ccc_e       cmd;
    logic     [3:0] tid;
    i3c_cmd_attr_e  cmd_attr;
  } i3c_xfer_cmd_reg_t;

  // Combo Transfer Command. Format 1 (TCRI 7.1.2.3).
  typedef struct packed {
    logic    [15:0] data_length;
    logic    [15:0] offset;
    logic           toc;
    logic           wroc;
    logic           rnw;
    i3c_xfer_mode_e mode;
    logic           suboff_16b;
    logic           fpm;
    logic     [1:0] dlp;
    logic           reserved;
    logic     [4:0] dev_index;
    logic           cp;
    i3c_ccc_e       cmd;
    logic     [3:0] tid;
    i3c_cmd_attr_e  cmd_attr;
  } i3c_xfer_cmd_combo_t;

  // Address Assignment Command. (HCI 8.4.1).
  typedef struct packed {
    logic    [31:0] reserved2;
    logic           toc;
    logic           wroc;
    logic     [3:0] dev_count;
    logic     [4:0] reserved1;
    logic     [4:0] dev_index;
    logic           reserved;
    i3c_ccc_e       cmd;
    logic     [3:0] tid;
    i3c_cmd_attr_e  cmd_attr;
  } i3c_xfer_cmd_addr_assgn_t;

  // Internal Control Command (HCI 8.4.2).
  typedef struct packed {
    logic    [31:0] vendor_specific;
    logic   [31:12] mipi_reserved;
    i3c_mipi_cmd_e  mipi_cmd;
    logic           vend_info_present;
    logic     [3:0] tid;
    i3c_cmd_attr_e  cmd_attr;
  } i3c_xfer_cmd_intern_ctrl_t;

  // Response Descriptor (TCRI 7.1.3).
  typedef struct packed {
    i3c_err_status_e err_status;
    logic      [3:0] tid;
    logic      [7:0] reserved;
    logic     [15:0] data_length;
  } i3c_xfer_rsp_t;

  // IBI Status Descriptor (HCI 8.6).
  typedef struct packed {
    logic             ibi_sts;
    logic             error;
    i3c_ibi_status_e  status_type;
    logic             reserved;
    logic             ts;
    logic             last_status;
    logic       [7:0] chunks;
    logic       [7:0] ibi_id;
    logic       [7:0] data_length;
  } i3c_ibi_status_t;

  // --- End of HCI/TCRI structure descriptions ---

  // --- HDR-DDR structure descriptions ---

  typedef struct packed {
    logic        rnw;        // 1: Read, 0: Write.
    logic [14:8] cmd_code;   // Command code.
    logic  [7:1] targ_addr;  // Dynamic address of target.
    logic        para;       // Parity Adjustment.
  } i3c_ddr_cmd_word_t;

  // --- End of HDR-DDR structure descriptions ---

  // --- Software updates of the Controller-side DAT cache ---

  typedef struct packed {
    logic [6:0] dyn_addr;     // Dynamic Address, no parity bit.
    logic       ibi_payload;  // IBI has an associated payload.
    logic       ibi_reject;   // Reject In-Band Interrupts from this address?
    logic       crr_reject;   // Reject Controller-Role Requests from this address?
  } i3c_datc_wdata_t;

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

  // Type of data unit transferred/request to be actioned.
  // TODO: It's likely that there's some benefit to splitting this into two types.
  // Then move them into controller/target_pkg.
  typedef enum logic [4:0] {
    // Time interval.
    I3CDType_TimedDelay   = 5'b00000,  // TODO: This seemed useful but presently is unused.
    // HDR-DDR Words; bits [1:0] are the Preamble bits.
    I3CDType_CommandWord  = 5'b00001,
    I3CDType_DataWord     = 5'b00011,
    I3CDType_CRCWord      = 5'b00101,
    // Arbitrable Address Header.
    I3CDType_ArbAddr      = 5'b00010,
    // Ack/Nack bit of arbitrable address header.
    I3CDType_AckNack      = 5'b00100,
    // Arbitrable Dynamic Address Allocation phase.
    I3CDType_ArbDAA       = 5'b00110,
    I3CDType_DynAddr      = 5'b00111,
    // Non-arbitrable Address Header.
    I3CDType_Address      = 5'b01000,
    // SDR signaling.
    I3CDType_SDRBytes     = 5'b01001,
    // SDRStop
    I3CDType_SDRStart     = 5'b01010,
    I3CDType_SDRStop      = 5'b01011,
    I3CDType_SDRRepStart  = 5'b01100,
    // HDR Restart/Exit signaling.
    I3CDType_HDRRestart   = 5'b01101,
    I3CDType_HDRExit      = 5'b01110,
    // Direct drive of SCL and SDA by software.
    I3CDType_DirectDrive  = 5'b01111,
    // Target Resdet signaling.
    I3CDType_TargetReset  = 5'b10000
  } i3c_dtype_e;

  // Group address description.
  typedef struct packed {
    logic            [6:0] addr;
    logic                  addr_valid;
    // Subset of Virtual Targets presently subscribed to this group address.
    logic [NumTargets-1:0] targets;
  } i3c_grp_addr_t;

  // Set maximum read, write, IBI length.
  typedef struct packed {
    logic                  setmwl;   // As opposed to SETMRL.
    logic                  setibi;   // Optional, SETMRL only.
    logic [NumTargets-1:0] targets;  // Set of affected Targets.
    logic           [15:0] mwrl;     // Length for SETMW|RL.
    logic            [7:0] ibil;     // Optional max IBI payload length.
  } i3c_setml_t;

  // Enable/Disable Target-side IBI generation.
  typedef struct packed {
    logic [NumTargets-1:0] enint;   // Regular In-Band Interrupts.
    logic [NumTargets-1:0] disint;
    logic [NumTargets-1:0] encr;    // Controller Role requests.
    logic [NumTargets-1:0] discr;
    logic [NumTargets-1:0] enhj;    // Hot-Join requests.
    logic [NumTargets-1:0] dishj;
  } i3c_endis_event_t;

  // Indicates whether the given address is an 'Error Type TE0' address (4.3.8.1.1).
  // - these are single-bit deviations from the I3C Broadcast Address 7'h7e.
  // TODO: Target-side logic checking using this function also needs to catch 7'h7e/R except when
  // handling ENTDAA (HCI 4.3.8.1.1).
  function automatic bit te0_invalid_addr(bit [6:0] addr);
    return (addr inside {7'h7f, 7'h7c, 7'h7a, 7'h76, 7'h6e, 7'h5e, 7'h3e});
  endfunction

  // Check whether the given I3C address is invalid before attempting to drive it out into an
  // arbitrable address header. This is primarily a safeguard against addressing any I2C device(s)
  // on the bus that are known to employ clock-stretching.
  //
  // TODO: Update this according to usage, include masks and parameterize for NumBlocked.
  function automatic bit invalid_addr(bit [6:0] addr,
                                      bit [6:0] blocked_addr0,
                                      bit [6:0] blocked_addr1,
                                      bit       target);
    case (addr)
      7'h00:         return 1'b1;
      7'h02:         return !target;  // Hot-Join requests permissible only from Targets.
      blocked_addr0: return 1'b1;
      blocked_addr1: return 1'b1;
      default:       return te0_invalid_addr(addr);
    endcase
    return 1'b0;
  endfunction

  // Return the length in bits of the given unit type, minus 1 for counting down.
  function automatic bit [Log2DW-1:0] unitlen_bits(i3c_dtype_e dtype);
    case (dtype)
      I3CDType_CommandWord,
      I3CDType_DataWord:   return Log2DW'(19);
      // CRC Words are 12 bits including the final setup bit ('1') for HDR Restart/Exit.
      I3CDType_CRCWord:    return Log2DW'(11);
      I3CDType_SDRBytes,
      I3CDType_Address,
      I3CDType_DynAddr,
      I3CDType_ArbAddr:    return Log2DW'(8);  // TODO: Decide whether to handle the ACK separately.
      I3CDType_ArbDAA:     return Log2DW'(7);  // No ACK bit in DAA reads.
      // Other requests may count down cycles during their operation, and perhaps consist of
      // multiple phases, but they are treated as single-bit units.
      default:             return Log2DW'(0);
    endcase
  endfunction

  // The use of some CCCs is absolutely prohibited in Command Descriptors (TCRI 6.2) because the
  // Host Controller issues them internally. (Note that some others are conditionally-blocked.)
  function automatic bit tcri_blocked_ccc(logic [7:0] ccc);
    case (ccc)
      ENTHDR0, ENTHDR1, ENTHDR2, ENTHDR3, ENTHDR4, ENTHDR5, ENTHDR6, ENTHDR7,
      GETACCCR: return 1'b1;
      default:  return 1'b0;
    endcase
  endfunction

  // Broadcast CCCs need to be treated differently, especially on the Target side.
  function automatic bit broadcast_ccc(logic [7:0] ccc);
    return !ccc[7];
  endfunction

  // Direct Get, as opposed to Direct Set or Broadcast CCC?
  function automatic bit direct_get(logic [7:0] ccc);
    return ccc[7] & (ccc inside {GETMWL, GETMRL, GETPID, GETBCR, GETDCR, GETSTATUS,
                                 GETACCCR, GETMXDS, GETCAPS, GETXTIME});
  endfunction

  // A small number of the CCCs have a Defining Byte, which precedes the write data in the event
  // of a Broadcast CCC.
  function automatic bit ccc_has_defb(logic [7:0] ccc);
    // Note that we need only be concerned with those CCCs that are supported by the Target;
    // the Target transceiver logic is responsible for rejecting or ignoring CCCs/DEFBs that are not
    // supported.
    return ccc inside {ENTTM, RSTACTB, GETSTATUS, ENDXFER, GETMXDS, GETCAPS, RSTACT};
  endfunction

  // Indicates whether the Target supports the given Direct Common Control Command.
  // - this is for use in deciding whether to ACK/NACK the Target/Group address, so it is not
  //   concerned with Broadcast CCCs.
  function automatic bit supported_direct_ccc(logic [7:0] ccc);
    return ccc inside {ENEC, DISEC, SETDASA, SETNEWDA, SETMWL, SETMRL, GETMWL, GETMRL, GETPID,
                       GETBCR, GETDCR, GETSTATUS, GETACCCR, ENDXFER, GETMXDS, GETCAPS, SETROUTE,
                       RSTACT, SETGRPA, RSTGRPA};
  endfunction

endpackage
