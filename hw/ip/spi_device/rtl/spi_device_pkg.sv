// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

package spi_device_pkg;

  // Passthrough Inter-module signals
  typedef struct packed {
    // passthrough_en: switch the mux for downstream SPI pad to host system not
    // the internal SPI_HOST IP
    logic       passthrough_en;

    // Passthrough includes SCK also. The sck_en is pad out enable not CG
    // enable. The CG is placed in SPI_DEVICE IP.
    logic       sck;
    logic       sck_gate_en; // TBD: place for CG?
    logic       sck_en;

    // CSb should be pull-up pad. In passthrough mode, CSb is directly connected
    // to the host systems CSb except when SPI_DEVICE decides to drop the
    // command.
    logic       csb;
    logic       csb_en;

    // SPI data from host system to downstream flash device.
    logic [3:0] s;
    logic [3:0] s_en;
  } passthrough_req_t;

  typedef struct packed {
    // SPI data from downstream flash device to host system.
    logic [3:0] s;
  } passthrough_rsp_t;

  parameter passthrough_req_t PASSTHROUGH_REQ_DEFAULT = '{
    passthrough_en: 1'b 0,
    sck:            1'b 0,
    sck_gate_en:    1'b 0,
    sck_en:         1'b 0,
    csb:            1'b 1,
    csb_en:         1'b 0,
    s:              4'h 0,
    s_en:           4'h 0
  };

  parameter passthrough_rsp_t PASSTHROUGH_RSP_DEFAULT = '{
    s: 4'h 0
  };

  // SPI Operation mode
  typedef enum logic [1:0] {
    FwMode      = 'h0,
    FlashMode   = 'h1,
    PassThrough = 'h2
  } spi_mode_e;

  // SPI IO mode
  typedef enum logic [1:0] {
    SingleIO = 2'h 0,
    DualIO   = 2'h 1,
    QuadIO   = 2'h 2
  } io_mode_e;
  typedef enum int unsigned {
    IoModeFw       = 0,
    IoModeCmdParse = 1,
    IoModeReadCmd  = 2,
    IoModeEnd      = 3 // Indicate of Length
  } sub_io_mode_e;

  // SPI Line Mode (Mode0 <-> Mode3)
  // This HWIP does not support Mode1 and Mode2
  typedef enum logic {
    // Mode0: CPOL=0, CPHA=0
    //  Data sampled on rising edge and shifted on falling edge
    LineMode0 = 1'b 0,
    // Mode3: CPOL=1, CPHA=1
    //  Data sampled on falling edge and shifted on rising edge
    LineMode3 = 1'b 1
  } line_mode_e;

  // SPI Read mode. QUAD uses additional two pins to read
  // Bit 0: Single, Bit 1: Dual Bit 2: Quad
  typedef logic [2:0] spi_rdmode_t;

  typedef logic [7:0] spi_byte_t;

  // eSPI utilizes Alert# signal (from device to host)
  typedef enum logic [1:0] {
    Spi    = 2'h0,
    Espi   = 2'h1,
    Tpm    = 2'h2
  } spi_type_e;

  typedef enum logic [1:0] {
    AddrByte = 2'h0,  // 1 byte for address
    AddrWord = 2'h1,  // 2 bytes for address
    AddrFull = 2'h2   // 3 bytes for address
  } spi_addr_size_e;

  localparam int MEM_AW = 12; // Memory Address width (Byte based)

  typedef enum logic [5:0] {
    DpNone       = 'b 000000,
    DpReadCmd    = 'b 000001,
    DpReadStatus = 'b 000010,
    DpReadSFDP   = 'b 000100,
    DpReadJEDEC  = 'b 001000,

    // Command + Address only: e.g Block Erase
    // Command + Address + Paylod: Program
    // Command followed by direct payload
    // Write Status could be an example
    // Command only: Write Protect Enable / Chip Erase
    DpUpload     = 'b 010000,
    // Unrecognizable commands: Just handle this as DpPayload
    DpUnknown    = 'b 100000
  } sel_datapath_e;

  typedef enum spi_byte_t {
    CmdNone = 8'h 00,

    CmdWriteStatus1 = 8'h 01,
    CmdWriteStatus2 = 8'h 31,
    CmdWriteStatus3 = 8'h 11,

    CmdReadStatus1 = 8'h 05,
    CmdReadStatus2 = 8'h 35,
    CmdReadStatus3 = 8'h 15,

    CmdJedecId = 8'h 9F,

    CmdPageProgram     = 8'h 02,
    CmdQuadPageProgram = 8'h 32, // Not supported

    CmdSectorErase  = 8'h 20, // 4kB erase
    CmdBlockErase32 = 8'h 52, // 32kB
    CmdBlockErase64 = 8'h D8, // 64kB

    CmdReadData   = 8'h 03,
    CmdReadFast   = 8'h 0B, // with Dummy
    CmdReadDual   = 8'h 3B,
    CmdReadQuad   = 8'h 6B,
    CmdReadDualIO = 8'h BB,
    CmdReadQuadIO = 8'h EB,

    CmdWriteDisable = 8'h 04,
    CmdWriteEnable  = 8'h 06,

    CmdReadSfdp = 8'h 5A,

    CmdEnableReset = 8'h 66,
    CmdResetDevice = 8'h 99
  } spi_cmd_e;

  // Sram parameters
  parameter int unsigned SramDw = 32;

  // Msg region is used for read cmd in Flash and Passthrough region
  parameter int unsigned SramMsgDepth = 512; // 2kB

  parameter int unsigned SramMailboxDepth = 256; // 1kB for mailbox

  // SPI Flash Discoverable Parameter is for host to get the device
  // information. It is a separate Command. The device provides a region in
  // DPSRAM for SW. The size is 256B
  parameter int unsigned SramSfdpDepth = 64;
  parameter int unsigned SramPayloadDepth = 64; // 256B for Program
  parameter int unsigned SramCmdFifoDepth = 16; // 16 x 1B for Cmd
  parameter int unsigned SramAddrFifoDepth = 16; // 16 x 4B for Addr
  parameter int unsigned SramTotalDepth = SramMsgDepth + SramMailboxDepth
                                        + SramSfdpDepth + SramPayloadDepth
                                        + SramCmdFifoDepth + SramAddrFifoDepth ;

  // Sram Depth is set to 1024 to satisfy DPSRAM parameter even though
  // SramTotalDepth above is 928.
  //parameter int unsigned SramDepth = 1024;

  parameter int unsigned SramAw = $clog2(spi_device_reg_pkg::SramDepth);

  typedef logic [SramAw-1:0] sram_addr_t;
  typedef struct packed {
    logic [SramDw-1:0]   data;
  } sram_data_t;
  typedef struct packed {
    logic uncorr;
    logic corr;
  } sram_err_t;

  // Calculate each space's base and size
  parameter sram_addr_t SramReadBufferIdx  = sram_addr_t'(0);
  parameter sram_addr_t SramReadBufferSize = sram_addr_t'(SramMsgDepth);

  parameter sram_addr_t SramMailboxIdx  = SramReadBufferIdx + SramReadBufferSize;
  parameter sram_addr_t SramMailboxSize = sram_addr_t'(SramMailboxDepth);

  parameter sram_addr_t SramSfdpIdx  = SramMailboxIdx + SramMailboxSize;
  parameter sram_addr_t SramSfdpSize = sram_addr_t'(SramSfdpDepth);

  parameter sram_addr_t SramPayloadIdx  = SramSfdpIdx + SramSfdpSize;
  parameter sram_addr_t SramPayloadSize = sram_addr_t'(SramPayloadDepth);

  parameter sram_addr_t SramCmdFifoIdx  = SramPayloadIdx + SramPayloadSize ;
  parameter sram_addr_t SramCmdFifoSize = sram_addr_t'(SramCmdFifoDepth);

  parameter sram_addr_t SramAddrFifoIdx  = SramCmdFifoIdx + SramCmdFifoSize ;
  parameter sram_addr_t SramAddrFifoSize = sram_addr_t'(SramAddrFifoDepth);

  // Max BitCount in a transaction
  parameter int unsigned BitLength = SramMsgDepth * 32;
  parameter int unsigned BitCntW   = $clog2(BitLength + 1);

  // spi device scanmode usage
  typedef enum logic [2:0] {
    ClkInvSel,
    CsbRstMuxSel,
    TxRstMuxSel,
    RxRstMuxSel,
    ClkMuxSel,
    ClkSramSel,
    RstSramSel,
    ScanModeUseLast
  } scan_mode_e;

endpackage : spi_device_pkg
