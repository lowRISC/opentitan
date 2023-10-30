// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds functional coverage interaface to the top level keymgr module.
module keymgr_cov_bind;

  bind keymgr cip_lc_tx_cov_if u_lc_escalate_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_keymgr_en_i)
  );
endmodule
