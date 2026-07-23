// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface kmac_if(input clk_i, input rst_ni);

  import kmac_env_pkg::*;

  logic                                          en_masking_o;
  lc_ctrl_pkg::lc_tx_t                           lc_escalate_en_i;
  prim_mubi_pkg::mubi4_t                         idle_o;

  function automatic void drive_lc_escalate(lc_ctrl_pkg::lc_tx_t val);
    lc_escalate_en_i = val;
  endfunction

  `ASSERT(KmacMaskingO_A, `EN_MASKING == en_masking_o)
endinterface
