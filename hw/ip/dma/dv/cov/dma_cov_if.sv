// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface dma_cov_if
  import dma_reg_pkg::*;
(
  input              clk,
  input dma_reg2hw_t reg2hw
);
  `include "dv_fcov_macros.svh"

endinterface
