// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Controller-side enumerations and structure definitions.

package i3c_controller_pkg;
  import i3c_consts_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
  import i3c_timing_pkg::*;

  // Present the `HC_CONTROL` state to the register API, renamed to make it less unwieldy as a port.
  typedef i3c_hw2reg_hc_control_reg_t hc_control_t;

  // Global state of the I3C Controller logic.
  // - this is managed by `i3c_controller_state` and presented to the Controller FSM logic.
  // - importantly, the `<x>ing` states are a persistent indication to the FSM of the intended
  //   course of action, rather than having to respond to a single-cycle request assertion in each
  //   affected state/transition of the FSM.
  typedef enum logic [2:0] {
    GState_Disabled,
    GState_Disabling,  // Await confirmation from the FSM.
    GState_Aborted,
    GState_Aborting,   // Await confirmation from the FSM.
    GState_Running,    // Entered from Disabled (BUS_ENABLE) or Suspended (RESUME).
    GState_Suspended   // Entered in response to an indication from the Controller FSM.
  } i3c_ctrl_gstate_e;

  // The type of transfer being performed by the Controller.
  typedef enum logic [1:0] {
    TransType_None,
    TransType_Cmd,  // Transfer is the result of executing a Command Descriptor.
    TransType_Intr  // Encompasses IBI, CRR and Hot-Join requests.
  } i3c_ctrl_trans_type_e;

  // Controller FSM states; this state machine handles the processing of HCI Command Descriptors and
  // the servicing of In-Band Interrupts.
  typedef enum logic [5:0] {
    Inactive,

    // --- Bus Idle events ---
    Idle,

    // --- Command/Response Transfers ---
    CmdBegin,   // Reading from Device Address Table when beginning a Command.
    DATCapt,    // Capture DAT entry, giving the properties of the device/group.
    CmdDecode,  // Full Command decoding, given the Command Descriptor and associated DAT entry.
    StartSDR,   // Issue SDR (S)tart signaling for a Command.
    StopSDR,    // Issue SDR sto(P) signaling.
    RepStSDR,   // Issue SDR repeated Start signaling.
    RepStPriv,  // Issue Repeated Start (Sr) after I3C Broadcast Address, before Private Transfer.
    CmdAddr,    // Sending I3C Broadcast Address, Target or Group address.
    CmdArb,     // As above but Arbitrable, i.e. following a Start.
    WaitArb,    // Awaiting result of Arbitration.
    WaitAckb,   // Collect Ack/Nack response to attempted Transfer.
    SendAckb,   // Send Ack/Nack response to IBI.
    EnterDDR,   // Sending ENTHDR0, which puts the bus into HDR-DDR mode.
    ExitHDR,    // Sending HDR Exit signaling, which returns the bus to SDR mode.
    ReStHDR,    // Sending HDR Restart signaling.
    CmdWord,    // Sending HDR-DDR Command Word.
    TxData,     // Moving data from Tx Buffer to Transceiver logic.
    TxCRC,      // Sending HDR-DDR CRC Word.
    RxData,     // Requesting read operations of the Transceiver logic.
    RxCRC,      // Receiving HDR-DDR CRC Word.

    // --- Controller Role and Hot-Join Requests ---
    CRR,        // TODO: CRR is not yet supported.
    HotJoin,    // Record Hot-Join request as an IBI Status Descriptor.

    // --- In-Band Interrupts ---
    IBICheck,   // Initial check of whether to accept or reject and IBI.
    IBIRxData,  // Request to the transfer to retrieve some IBI payload data.
    IBIRxWait,  // Await read data or transfer response from the transceiver.

    // --- CCC Handling ---
    CCC,        // The FSM remains in this state until the CCC has completed.

    // --- Target reset ---
    TargRst,    // Generate Target Reset signaling.

    // --- Direct drive by software; test/recovery ---
    DirectDrv,

    // --- Error handling and recovery ---
    CmdDecErr,  // Command was rejected in second-stage decoding.

    // Exit from this state occurs only in response to a software reset.
    ErrFatal
  } i3c_ctrl_fsm_state_e;

  // --- Requests to the transceiver logic ---

  // Type of request to the transceiver logic.
  // - these requests translate to specific units/signaling patterns on the I3C bus.
  typedef enum logic [3:0] {
    // HDR-DDR Words; bits [1:0] are the Preamble bits.
    CReqType_CommandWord  = 4'b0001,
    CReqType_DataWord     = 4'b0011,
    CReqType_CRCWord      = 4'b0101,
    // Arbitrable Address Header.
    CReqType_ArbAddr      = 4'b0010,
    // Ack/Nack bit of arbitrable address header.
    CReqType_AckNack      = 4'b0100,
    // Arbitrable Dynamic Address Allocation phase.
    CReqType_ArbDAA       = 4'b0110,
    CReqType_DynAddr      = 4'b0111,
    // Non-arbitrable Address Header.
    CReqType_Address      = 4'b1000,
    // SDR signaling.
    CReqType_SDRBytes     = 4'b1001,
    // SDRStop
    CReqType_SDRStart     = 4'b0000,
    CReqType_SDRStop      = 4'b1011,
    CReqType_SDRRepStart  = 4'b1100,
    // HDR Restart/Exit signaling.
    CReqType_HDRRestart   = 4'b1101,
    CReqType_HDRExit      = 4'b1110,
    // Direct drive of SCL and SDA by software.
    CReqType_DirectDrive  = 4'b1010,
    // Target Resdet signaling.
    CReqType_TargetReset  = 4'b1111
  } i3c_ctrl_req_e;

  // Description of a Controller transceiver request.
  typedef struct packed {
    // Request type.
    i3c_ctrl_req_e      req;
    // Timing parameters, as appropriate for the target and mode.
    i3c_ctrl_timing_t   tm;
    // Indicates whether we have not yet sent an I3C Broadcast Address successfully.
    // - until such an address is ACKed transmission occurs using slower signaling.
    logic               i3c_first;
    // Reception, not transmission.
    logic               rx;
    // Write data.
    logic      [DW-1:0] wdata;
    // Transfer length, as 'bytes minus 1' for Tx/Rx Data, or 'repetitions' for other requests.
    // - `wdata` has been padded to be whole units, but the response must be in bytes in order to
    //   support transfers of odd length in HDR-DDR mode too.
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
  // TODO: For the Controller we are quite likely to want to combine read data and response to
  // assist with producing an accurate count of the _write data_ transferred.
  typedef struct packed {
    // Indicates whether the data was retrieved in DDR mode.
    logic               ddr;
    // Response data.
    logic      [DW-1:0] rdata;
    logic  [Log2DW-3:0] rlen;  // Number of bytes outstanding, [0:4].
    // Last response of transfer?
    logic               rlast;
    // Early termination and error status.
    logic               rearly;
    logic               rerr;
  } i3c_ctrl_trx_rdata_t;

  // Description of a Controller transceiver response.
  typedef struct packed {
    // Response type, indicating any error condition,
    // or successful completion of the following requests:
    // - CReqType_CRCWord (tx or rx)
    // - CReqType_SDRStop
    // - CReqType_SDRRepStart
    i3c_err_status_e   err_status;
    // Number of units written.
    logic [Log2DW-3:0] wlen;
    logic              wearly;
    logic              werr;
  } i3c_ctrl_trx_rsp_t;

  // Software updates of the Controller-side DAT cache
  typedef struct packed {
    logic     [6:0] dyn_addr;      // Dynamic Address, no parity bit.
    logic           ibi_payload;   // IBI has an associated payload.
    logic           ibi_reject;    // Reject In-Band Interrupts from this address?
    logic           crr_reject;    // Reject Controller-Role Requests from this address?
    i3c_xfer_mode_e autocmd_mode;  // Transfer mode for this Target/Group; this is used for IBI
                                   // payload fetching, and is therefore implicitly an I3C bus mode.
  } i3c_datc_wdata_t;

  // Current state of the I3C bus, maintained by the Controller FSM.
  typedef struct packed {
    // Before the current command, until the mode has been switched.
    i3c_xfer_mode_e mode;
    logic           i2c;
  } i3c_ctrl_bus_state_t;

  // These command attributes are derived combinationally from the Command Descriptor and remain
  // valid throughout the processing of the command; there is no additional storage associated
  // with them.
  typedef struct packed {
    // Type of Command Descriptor (`attr` field).
    i3c_cmd_attr_e       attr;

    // Fields that are common to most/all command types.
    logic          [3:0] tid;        // Transaction ID.
    logic                wroc;       // Write Response on Completion?
    i3c_ccc_e            ccc;        // Common Command Code.

    // Fields that may be modified by the command type.
    i3c_xfer_mode_e      mode;       // Transfer mode.
    logic                rnw;        // Read, not Write in this command phase?
    logic                toc;        // Terminate On Completion (send stoP as opposed to Sr)?
    logic                i2c;        // I2C device, rather than I3C?
    logic                is_ccc;     // Common Command Code transfer?
    logic                brd_ccc;    // More specifically, is this a Broadcast CCC?
    logic                ddr;        // Use HDR-DDR mode this transfer?
    logic                has_defb;   // Does this command have an associated Defining Byte?
    logic          [7:0] defb;       // Defining Byte, if present.
    logic         [15:0] data_len;   // The number of data bytes being transferred.
    logic [DATAddrW-1:0] dev_index;  // Index into the DAT for this command phase.
    logic          [1:0] retry_cnt;  // Number of retries of this command when NACK(s) are received.
    logic  [CmdRepW-1:0] reps_left;  // Repetitions/phases left _after_ the current one.
  } i3c_ctrl_cmd_attrs_t;

  // Stored properties of the current HCI Command Descriptor, and properties preserved from earlier
  // Command Descriptor(s) forming a single Common Command Code transfer.
  //
  // - Command Descriptors may operate together to form a single CCC operation.
  // - Address Assignment commands require iteration, to assign a number of dynamic addresses.
  typedef struct packed {
    // Command Descriptor available; command ready to be actioned.
    // Note: This does not imply that the Command Descriptor has been accepted as valid.
    logic                 available;
    // Indication that the command has been accepted as valid and that we have started at least
    // one attempt at executing the command, so the remainder of this state may be trusted.
    logic                 started;

    // ----- The remaining fields are only valid if `started` is true. -----
    //
    // Was the most recent command/segment terminated with Sr rather than P?
    logic                 rep_start;
    // Number of retries required for this command when NACK(s) are received.
    logic           [1:0] retry_cnt;
    // Number of repetitions remaining.
    // - each repetition is a phase within e.g. a Combo Transfer or Address Assignment command.
    logic   [CmdRepW-1:0] reps_left;
    // Current DAT index; this advances whilst executing Address Assignment commands.
    logic  [DATAddrW-1:0] dev_index;
    // Command Descriptors performing a series of RSTACT CCCs are to be followed by the Target Reset
    // Pattern if it is not interrupted by failure or timeout.
    logic                 rst_csect;  // HCI 6.15.1
  } i3c_ctrl_cmd_state_t;

  // The standard Command Descriptors specify a transfer more and an I2C/I3C indication, which
  // together determine the signaling rate and bus mode.
  // - some possible encodings are undefined, and this IP does not support HDR Ternary signaling.
  function automatic logic mode_supported(logic [2:0] mode, logic i2c);
    return i2c ? (mode <= XferMode_I2CUDR3) : !(mode inside {XferMode_HDRTernary, 3'h7});
  endfunction

endpackage
