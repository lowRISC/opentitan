// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package top_pkg;

localparam int TL_AW=32;
localparam int TL_DW=32;    // = TL_DBW * 8; TL_DBW must be a power-of-two
localparam int TL_AIW=8;    // a_source, d_source
localparam int TL_DIW=1;    // d_sink
localparam int TL_AUW=21;   // a_user
localparam int TL_DUW=14;   // d_user
localparam int TL_DBW=(TL_DW>>3);
localparam int TL_SZW=$clog2($clog2(TL_DBW)+1);

// NOTE THAT THIS IS A FEATURE FOR TEST CHIPS ONLY TO MITIGATE
// THE RISK OF A BROKEN OTP MACRO. THIS WILL BE DISABLED FOR
// PRODUCTION DEVICES.
localparam int SecVolatileRawUnlockEn = 1;

// TODO: Set the CTN SRAM to the same size as the discrete flash (2 x 512kB). We currently set
// this to 1kB to keep the FPGA build alive until the flash_ctrl can be removed.
localparam int CtnSramSize = 1024; // 2 * 512 * 1024;
localparam int CtnSramDepth = CtnSramSize / TL_DBW;
localparam int CtnSramAw = prim_util_pkg::vbits(CtnSramDepth);

// Addresses leaving the RoT have an internal 1G address space of 0x4000_0000 - 0x8000_0000.
// However, the address base is already filtered away by the SoC proxy module, hence valid
// requests are mapped to the 1G space are already filtered through the SoC proxy module, and
// thus they are mapped to the range 0x0000_0000 - 0x4000_0000 at this point.
// The CTN SRAM covers a 1MB memory range of mapped to 0x0100_0000 - 0x0110_0000.
localparam logic [TL_AW-1:0] CtnSramAddrMask = CtnSramSize - 1;
localparam logic [TL_AW-1:0] CtnSramAddrBase = 32'h01000000;

endpackage
