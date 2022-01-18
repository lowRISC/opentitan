// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds entropy_src functional coverage interface to the top-level entropy_src module.
module entropy_src_cov_bind;

  bind entropy_src entropy_src_cov_if u_entropy_src_cov_if (.*);

endmodule
