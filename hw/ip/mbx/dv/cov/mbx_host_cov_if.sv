// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface mbx_host_cov_if
  import mbx_reg_pkg::*;
(
  input              clk,
  input mbx_core_reg2hw_t reg2hw,
  input mbx_core_hw2reg_t hw2reg 
);
  `include "dv_fcov_macros.svh"
  //FIXME: add mbx top functional coverage

endinterface
