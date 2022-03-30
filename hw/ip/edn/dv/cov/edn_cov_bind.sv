// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds edn functional coverage interface to the top-level edn module.
module edn_cov_bind;

  bind edn edn_cov_if u_edn_cov_if (
    .clk_i    (clk_i),
    .ep_req   ({edn_i[6].edn_req, edn_i[5].edn_req, edn_i[4].edn_req, edn_i[3].edn_req,
                edn_i[2].edn_req, edn_i[1].edn_req, edn_i[0].edn_req})
  );

endmodule
