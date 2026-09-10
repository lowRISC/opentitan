// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_ram_1p_pkg;

  parameter int unsigned Ram1pReqWidth = 32'd13;
  parameter int unsigned Ram1pRspWidth = 32'd1;

  typedef struct packed {
    logic [Ram1pReqWidth-1:0] req;
  } ram_1p_cfg_req_t;

  typedef struct packed {
    logic [Ram1pRspWidth-1:0] rsp;
  } ram_1p_cfg_rsp_t;

  parameter ram_1p_cfg_req_t RAM_1P_CFG_REQ_DEFAULT = '0;
  parameter ram_1p_cfg_rsp_t RAM_1P_CFG_RSP_DEFAULT = '0;

endpackage // prim_ram_1p_pkg
