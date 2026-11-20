// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_ram_1r1w_pkg;

  // The SPI device can be switched to either use 1r1w or true 2p memories. To ensure
  // a compatibility between the two choices without increasing the parametrization effort,
  // derive the 1r1w type from the 2p.
  parameter int unsigned Ram1r1wReqWidth = prim_ram_2p_pkg::Ram2pReqWidth;
  parameter int unsigned Ram1r1wRspWidth = prim_ram_2p_pkg::Ram2pRspWidth;

  typedef prim_ram_2p_pkg::ram_2p_cfg_req_t ram_1r1w_cfg_req_t;
  typedef prim_ram_2p_pkg::ram_2p_cfg_rsp_t ram_1r1w_cfg_rsp_t;

  parameter ram_1r1w_cfg_req_t RAM_1R1W_CFG_REQ_DEFAULT = '0;
  parameter ram_1r1w_cfg_rsp_t RAM_1R1W_CFG_RSP_DEFAULT = '0;

endpackage // prim_ram_1r1w_pkg
