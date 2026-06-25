// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_rom_pkg;

  parameter int unsigned RomReqWidth = 32'd4;
  parameter int unsigned RomRspWidth = 32'd1;

  typedef struct packed {
    logic [RomReqWidth-1:0] req;
  } rom_cfg_req_t;

  typedef struct packed {
    logic [RomRspWidth-1:0] rsp;
  } rom_cfg_rsp_t;

  parameter rom_cfg_req_t ROM_CFG_REQ_DEFAULT = '0;
  parameter rom_cfg_rsp_t ROM_CFG_RSP_DEFAULT = '0;

endpackage // prim_rom_pkg
