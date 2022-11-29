// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds icache functional coverage interface to the top-level ibex_icache
// module.
module ibex_icache_fcov_bind;
  bind ibex_icache ibex_icache_fcov_if#(
    .NUM_FB(NUM_FB)
  ) u_ibex_icache_fcov_if (.*);
endmodule
