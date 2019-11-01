// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package top_pkg;

localparam TL_AW=32;
localparam TL_DW=32;    // = TL_DBW * 8; TL_DBW must be a power-of-two
localparam TL_AIW=8;    // a_source, d_source
localparam TL_DIW=1;    // d_sink
localparam TL_DUW=16;   // d_user
localparam TL_DBW=(TL_DW>>3);
localparam TL_SZW=$clog2($clog2(TL_DBW)+1);
localparam FLASH_BANKS=2;
localparam FLASH_PAGES_PER_BANK=256;
localparam FLASH_WORDS_PER_PAGE=256;
localparam FLASH_BYTES_PER_WORD=4;
localparam FLASH_BKW = $clog2(FLASH_BANKS);
localparam FLASH_PGW = $clog2(FLASH_PAGES_PER_BANK);
localparam FLASH_WDW = $clog2(FLASH_WORDS_PER_PAGE);
localparam FLASH_AW = FLASH_BKW + FLASH_PGW + FLASH_WDW;
localparam FLASH_DW = FLASH_BYTES_PER_WORD * 8;

endpackage
