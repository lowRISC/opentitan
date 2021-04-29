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
endpackage
