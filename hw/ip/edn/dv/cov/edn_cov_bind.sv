// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds edn functional coverage interface to the top-level edn module.
module edn_cov_bind;

  // Note that the coverage module has a max footprint design, so its edn_i port will be wider than
  // the edn_i signal that it's sampling. This will be extended with zeros and the actual number of
  // endpoints is supplied by an integral num_endpoints_i port, driven by a parameter at the bind
  // site.
  bind edn edn_cov_if u_edn_cov_if (
    .clk_i           (clk_i),
    .edn_i           (edn_i),
    .num_endpoints_i (NumEndPoints)
  );

endmodule
