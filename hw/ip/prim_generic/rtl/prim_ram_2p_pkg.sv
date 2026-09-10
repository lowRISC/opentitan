// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_ram_2p_pkg;

  parameter int unsigned Ram2pReqWidth = 32'd10;
  parameter int unsigned Ram2pRspWidth = 32'd1;

  typedef struct packed {
    logic [Ram2pReqWidth-1:0] req;
  } ram_2p_cfg_req_t;

  typedef struct packed {
    logic [Ram2pRspWidth-1:0] rsp;
  } ram_2p_cfg_rsp_t;

  parameter ram_2p_cfg_req_t RAM_2P_CFG_REQ_DEFAULT = '0;
  parameter ram_2p_cfg_rsp_t RAM_2P_CFG_RSP_DEFAULT = '0;

endpackage // prim_ram_2p_pkg
