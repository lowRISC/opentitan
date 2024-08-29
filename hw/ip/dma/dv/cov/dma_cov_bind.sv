// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module dma_cov_bind;
  bind dma dma_cov_if u_dma_cov_if (.clk(clk_i), .reg2hw);
endmodule
