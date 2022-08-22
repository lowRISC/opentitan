// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface kmac_if(input clk_i, input rst_ni);

  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i;

  prim_mubi_pkg::mubi4_t idle_o;
  logic en_masking_o;
  logic [kmac_pkg::NumAppIntf-1:0] app_err_o;

  function automatic void drive_lc_escalate(lc_ctrl_pkg::lc_tx_t val);
    lc_escalate_en_i = val;
  endfunction

  `ASSERT(KmacMaskingO_A, `EN_MASKING == en_masking_o)

  // TODO(#10804): confirm with designer if we need to set app_err_o as error.
  // `ASSERT(LcEscalationAppErr_A, lc_escalate_en_i != lc_ctrl_pkg::Off |->
  //        ##3 ((app_err_o == 3'b111) throughout (rst_ni == 1)))
endinterface
