// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds PATTGEN functional coverage interaface to the top level PATTGEN module.
module pattgen_cov_bind;

  bind pattgen pattgen_cov_if u_pattgen_cov_if (.*);

endmodule
