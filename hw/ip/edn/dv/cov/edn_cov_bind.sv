// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds edn functional coverage interface to the top-level edn module.
module edn_cov_bind;

  bind edn edn_cov_if u_edn_cov_if (.*);

endmodule
