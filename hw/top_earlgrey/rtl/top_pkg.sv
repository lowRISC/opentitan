// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package top_pkg;

localparam int TL_AW=32;
localparam int TL_DW=32;    // = TL_DBW * 8; TL_DBW must be a power-of-two
localparam int TL_AIW=8;    // a_source, d_source
localparam int TL_DIW=1;    // d_sink
localparam int TL_AUW=23;   // a_user
localparam int TL_DUW=14;   // d_user
localparam int TL_DBW=(TL_DW>>3);
localparam int TL_SZW=$clog2($clog2(TL_DBW)+1);

// Number of cycles a differential skew is tolerated on the alert signal
localparam int unsigned AlertSkewCycles = 1;

// The volatile RAW unlock is needed on this top to reach the RRAM forming flow.
// An unformed RRAM cannot hold a persistent life cycle state, so the part has to be unlocked
// volatilely to form it.
// lc_ctrl only accepts a volatile RAW unlock while rram_macro's allow_vol_unlock is True, which
// is the case until the DIS_VOL_RAW_UNLOCK marker is written at the end of forming.
localparam int SecVolatileRawUnlockEn = 1;

endpackage
