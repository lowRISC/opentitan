// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
interface rv_dm_if();

  import rv_dm_params_pkg::*;

  logic testmode;
  logic ndmreset;
  logic dmactive;
  logic [rv_dm_params_pkg::NR_HARTS-1:0] debug_req;
  logic [rv_dm_params_pkg::NR_HARTS-1:0] unavailable;

endinterface
