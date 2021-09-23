// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds csrng functional coverage interaface to the top level csrng module.
module csrng_cov_bind;

  bind csrng csrng_cov_if u_csrng_cov_if (.*);

endmodule
