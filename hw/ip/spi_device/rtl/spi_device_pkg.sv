// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

package spi_device_pkg;

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

  // List of supported commands @ Bunker mode (SPI Manufacturing mode)
  typedef enum logic [7:0] {
    Nop    = 8'h00,
    WrSts  = 8'h01,   // Write STATUS1 followed by STATUS2 register
    Write  = 8'h02,   // Write Data
    Read   = 8'h03,   // Limit to a certain speed as read data starts right after addr
    WrDi   = 8'h04,   // Write Disable: Clear WEL to 0
    RdSts  = 8'h05,
    WrEn   = 8'h06,   // Write Enable: Set WEL to 1
    HsRd   = 8'h0B,   // 8 cycle gap between addr/ rdata
    RdSts2 = 8'h35,   // Read STATUS2 register
    DlRd   = 8'h3B,   // Dual Read
    QdRd   = 8'h6B    // Quad Read
  } spi_rom_cmd_e;

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

  // spi device scanmode usage
  typedef enum logic [2:0] {
    ClkInvSel,
    CsbRstMuxSel,
    TxRstMuxSel,
    RxRstMuxSel,
    ClkMuxSel,
    ScanModeUseLast
  } scan_mode_e;

endpackage : spi_device_pkg
