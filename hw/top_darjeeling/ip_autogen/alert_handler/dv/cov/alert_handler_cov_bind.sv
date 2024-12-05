// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds ALERT_HANDLER functional coverage interafaces to the top level ALERT_HANDLER module.

module alert_handler_cov_bind;
  import alert_pkg::*;

  bind alert_handler cip_mubi_cov_wrapper#(.NumMubis(NLpg)) u_lpg_cg_en_cov_if (
    .rst_ni (rst_ni),
    .mubis  (lpg_cg_en_i)
  );

  bind alert_handler cip_mubi_cov_wrapper#(.NumMubis(NLpg)) u_lpg_rst_en_cov_if (
    .rst_ni (rst_ni),
    .mubis  (lpg_rst_en_i)
  );
endmodule : alert_handler_cov_bind
