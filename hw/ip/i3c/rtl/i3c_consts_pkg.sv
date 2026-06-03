// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Constants defined by the I3C Specifications rather than this IP block.
package i3c_consts_pkg;

  // Special I3C Addresses
  typedef enum logic [6:0] {
    Addr_MinimalBus = 7'h01,  // Target on Minimal Bus
    Addr_Broadcast  = 7'h7e   // I3C Broadcast Address
  } i3c_addr_e;

  // Common Command Codes
  typedef enum logic [7:0] {
    // Broadcast
    ENECB     = 8'h00,  // Enable Events Command
    DISECB    = 8'h01,  // Disable Events Command

    ENTAS0B   = 8'h02,  // Enter Activity State 0
    ENTAS1B   = 8'h03,  // Enter Activity State 1
    ENTAS2B   = 8'h04,  // Enter Activity State 2
    ENTAS3B   = 8'h05,  // Enter Activity State 3

    RSTDAA    = 8'h06,  // Reset Dynamic Address Assignment
    ENTDAA    = 8'h07,  // Enter Dynamic Address Assignment
    DEFTGTS   = 8'h08,  // Define List of Targets
    SETMWLB   = 8'h09,  // Set Max Write Length
    SETMRLB   = 8'h0a,  // Set Max Read Length
    ENTTM     = 8'h0b,  // Enter Test Mode

    ENTHDR0   = 8'h20,  // Enter HDR Mode 0
    ENTHDR1   = 8'h21,  // Enter HDR Mode 1
    ENTHDR2   = 8'h22,  // Enter HDR Mode 2
    ENTHDR3   = 8'h23,  // Enter HDR Mode 3
    ENTHDR4   = 8'h24,  // Enter HDR Mode 4
    ENTHDR5   = 8'h25,  // Enter HDR Mode 5
    ENTHDR6   = 8'h26,  // Enter HDR Mode 6
    ENTHDR7   = 8'h27,  // Enter HDR Mode 7

    SETAASA   = 8'h29,  // Set All Addresses to Static Addresses
    RSTACTB   = 8'h2a,  // Target Reset Action
    DEFGRPA   = 8'h2b,  // Define List of Group Addresses
    RSTGRPAB  = 8'h2c,  // Reset Group Address
    MLANEB    = 8'h2d,  // Multi-Lane Data Transfer Control

    // Directed
    ENEC      = 8'h80,  // Enable Events Command
    DISEC     = 8'h81,  // Disable Events Command

    ENTAS0    = 8'h82,  // Enter Activity State 0
    ENTAS1    = 8'h83,  // Enter Activity State 1
    ENTAS2    = 8'h84,  // Enter Activity State 2
    ENTAS3    = 8'h85,  // Enter Activity State 3

    SETDASA   = 8'h87,  // Set Dynamic Address from Static Address
    SETNEWDA  = 8'h88,  // Set New Dynamic Address
    SETMWL    = 8'h89,  // Set Max Write Length
    SETMRL    = 8'h8a,  // Set Max Read Length
    GETMWL    = 8'h8b,  // Get Max Write Length
    GETMRL    = 8'h8c,  // Get Max Read Length
    GETPID    = 8'h8d,  // Get Provisioned ID
    GETBCR    = 8'h8e,  // Get Bus Characteristics Register
    GETDCR    = 8'h8f,  // Get Device Characteristics Register
    GETSTATUS = 8'h90,  // Get Device Status
    GETACCCR  = 8'h91,  // Get Accept Controller Role
    ENDXFER   = 8'h92,  // Data Transfer Ending Procedure Control

    GETMXDS   = 8'h94,  // Get Max Data Speed
    GETCAPS   = 8'h95,  // Get Optional Feature Capabilities
    SETROUTE  = 8'h96,  // Set Route

    SETXTIME  = 8'h98,  // Set Exchange Timing Information
    GETXTIME  = 8'h99,  // Get Exchange Timing Information

    RSTACT    = 8'h9a,  // Target Reset Action
    SETGRPA   = 8'h9b,  // Set Group Address
    RSTGRPA   = 8'h9c,  // Reset Group Address
    MLANE     = 8'h9d   // Multi-Lane Data Transfer Control
  } i3c_ccc_e;

  // RSTACT Defining Byte Values (5.1.9.3.26)
  typedef enum logic [7:0] {
    RstAct_NoReset         = 8'h00, // No Reset on Target Reset Pattern.
    RstAct_ResetPeripheral = 8'h01, // Reset the I3C Peripheral Only.
    RstAct_ResetTarget     = 8'h02, // Reset the Whole Target.
    RstAct_DebugNetReset   = 8'h03, // Debug Network Adapter Reset.
    RstAct_VirtualTargDet  = 8'h04, // Virtual Target Detect.
    RstAct_ResetPeriphTime = 8'h81, // Return Time to Reset Peripheral.
    RstAct_ResetTargetTime = 8'h82, // Return Time to Reset Whole Target.
    RstAct_ResetDbgNetTime = 8'h83, // Return Time for Debug Network Adapter Reset.
    RstAct_VirtTargIndican = 8'h84  // Return Virtual Target Indication.
  } i3c_rstact_e;

  // I3C Transfer Mode (TCRI 7.1.1.1)
  typedef enum logic [2:0] {
    XferMode_SDR0       = 3'h0,  // 12.5 MHz maximum sustainable data rate.
    XferMode_SDR1       = 3'h1,  // 8 MHz
    XferMode_SDR2       = 3'h2,  // 6 MHz
    XferMode_SDR3       = 3'h3,  // 4 MHz
    XferMode_SDR4       = 3'h4,  // 2 MHz
    XferMode_HDRTernary = 3'h5,
    XferMode_HDRDDR     = 3'h6
  } i3c_xfer_mode_e;

  // I2C Transfer Mode (TCRI 7.1.1.1)
  typedef enum logic [2:0] {
    XferMode_I2CFM      = 3'h0,  // 400 kHz maximum sustainable data rate.
    XferMode_I2CFMPlus  = 3'h1,  // 1 MHz
    XferMode_I2CUDR1    = 3'h2,  // User Defined Data Rate 1
    XferMode_I2CUDR2    = 3'h3,
    XferMode_I2CUDR3    = 3'h4
  } i2c_xfer_mode_e;

  // CMD_ATTR field of Command Descriptor (TCRI 7.1.2)
  typedef enum logic [2:0] {
    CmdAttr_RegTransfer    = 3'h0,
    CmdAttr_ImmTransfer    = 3'h1,
    CmdAttr_AddrAssignment = 3'h2,
    CmdAttr_ComboTransfer  = 3'h3,
    CmdAttr_InternalCtrl   = 3'h7
  } i3c_cmd_attr_e;

  // Error Status Codes (TCRI 6.4.1)
  typedef enum logic [3:0] {
    ErrStatus_OK = 4'h0,
    ErrStatus_CRC,
    ErrStatus_Parity,
    ErrStatus_Frame,
    ErrStatus_AddrHeader,
    ErrStatus_NACK,
    ErrStatus_OVL,
    ErrStatus_I3CShortReadErr,
    ErrStatus_HCAborted,
    ErrStatus_BusAborted = 4'h9,  // Overloaded; see below for I2C traffic.
    ErrStatus_NotSupported,
    ErrStatus_AbortedWithCRC,

    // The following are Transfer Type Specific (Combo Transfers).
    ErrStatus_ComboNACK2nd = 4'hC,   // Overloaded below; transfer-type specific.
    ErrStatus_ComboBusAborted2nd
  } i3c_err_status_e;

  // This value is overloaded, having different meanings for I2C and I3C transfers.
  localparam i3c_err_status_e ErrStatus_I2cWrDataNack = i3c_err_status_e'(4'h9);
  // This value is overloaded, being Transfer Type Specific (TCRI 6.4.1.12).
  localparam i3c_err_status_e ErrStatus_CccFramingNotEnded = i3c_err_status_e'(4'hC);

  // IBI Status Types (HCI 8.6)
  typedef enum logic [2:0] {
    IBIStatus_Regular       = 3'b000,
    IBIStatus_CreditAck     = 3'b001,
    IBIStatus_ScheduledCmd  = 3'b010,
    IBIStatus_AutoCmdRead   = 3'b100,
    IBIStatus_StbyCrBastCCC = 3'b111
  } i3c_ibi_status_e;

  // Host Controller Secondary Controller enable (HCI 7.7.11.1)
  typedef enum logic [1:0] {
    StbyCrEn_Disabled = 2'b00,
    StbyCrEn_ACMInit,
    StbyCrEn_SCMRunning,
    StbyCrEn_SCMHotJoin
  } i3c_stby_cr_en_init_e;

  // Present State Debug (HCI 7.7.7.3)
  // Bus Controller Logic Transfer State
  typedef enum logic [5:0] {
    BCLState_Idle = 6'h0,
    BCLState_Start,
    BCLState_Restart,
    BCLState_Stop,
    BCLState_StartHold,
    BCLState_BcastWrite,
    BCLState_BcastRead,
    BCLState_DAA,
    BCLState_Addr,
    BCLState_CCC = 6'hB,
    BCLState_HDR,
    BCLState_Wr,
    BCLState_Rd,
    BCLState_IBIAdrRead,
    BCLState_IBIDis,
    BCLState_HDRDDRCRC,
    BCLState_ClockExt,
    BCLState_Halt,
    BCLState_IBIRead
  } i3c_bcl_tfr_ststat_e;

  typedef enum logic [5:0] {
    BCLStatus_Idle = 6'h0,
    BCLStatus_BcastWrite,
    BCLStatus_TargetWrite,
    BCLStatus_TargetRead,
    BCLStatus_EntDAA,
    BCLStatus_SetDASA,
    BCLStatus_I3CSDRWrite,
    BCLStatus_I3CSDRRead,
    BCLStatus_I2CSDRWrite,
    BCLStatus_I2CSDRRead,
    // Ternary states not required.
    BCLStatus_HDRDDRWrite = 6'hC,
    BCLStatus_HDRDDRRead,
    BCLStatus_IBI,
    BCLStatus_Halted
  } i3c_bcl_tfr_status_e;

  // MIPI Alliance Command (HCI 8.4.2, Table 135).
  typedef enum logic [3:0] {
    MIPICmd_NoOp = 4'h0,
    MIPICmd_RingBundleLock,
    MIPICmd_BroadAddrEnable,
    MIPICmd_DevCtxUpdate,
    MIPICmd_TargRstPattern,
    MIPICmd_CtrlSDARecovery,
    MIPICmd_EndXferHDR,
    MIPICmd_CtrlHandoff,
    MIPICmd_AttemptDBR = 4'hD
  } i3c_mipi_cmd_e;

  // Target Reset Operation Type (HCI 8.4.2.4)
  typedef enum logic [1:0] {
    RstOpType_Single = 2'b00,
    RstOpType_Reserved,
    RstOpType_RSTACC,
    RstOpType_Leave
  } i3c_reset_op_type_e;

endpackage
