// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
interface flash_ctrl_dv_if (
  input logic clk_i,
  input logic rst_ni
);

  import flash_ctrl_pkg::*;
  import lc_ctrl_pkg::*;

  logic       rd_buf_en;
  lc_tx_t rma_req;
  rma_state_e rma_state;
  logic [10:0] prog_state0;
  logic [10:0] prog_state1;
  logic [10:0] lcmgr_state;

endinterface
