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
    EepromRam   = 'h1,
    EepromFlash = 'h2,
    PassThrough = 'h3
  } spi_mode_e;

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

endpackage : spi_device_pkg
