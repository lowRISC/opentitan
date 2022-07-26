// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
import flash_ctrl_pkg::*;
import lc_ctrl_pkg::*;
interface flash_ctrl_dv_if (
  input logic clk_i,
  input logic rst_ni,
  input logic rd_buf_en,
  input lc_tx_t rma_req,
  input rma_state_e rma_state,
  input logic [10:0] lcmgr_state
);

endinterface
