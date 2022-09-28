// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface kmac_if(input clk_i, input rst_ni);

  import kmac_env_pkg::*;

  logic                                          en_masking_o;
  lc_ctrl_pkg::lc_tx_t                           lc_escalate_en_i;
  prim_mubi_pkg::mubi4_t                         idle_o;
  kmac_pkg::app_req_t [kmac_pkg::NumAppIntf-1:0] app_req;
  kmac_pkg::app_rsp_t [kmac_pkg::NumAppIntf-1:0] app_rsp;

  function automatic void drive_lc_escalate(lc_ctrl_pkg::lc_tx_t val);
    lc_escalate_en_i = val;
  endfunction

  `ASSERT(KmacMaskingO_A, `EN_MASKING == en_masking_o)

  `ASSERT(AppKeymgrErrOutputZeros_A, app_rsp[AppKeymgr].error |->
          app_rsp[AppKeymgr].digest_share0 == 0 && app_rsp[AppKeymgr].digest_share1 == 0)

  `ASSERT(AppLcErrOutputZeros_A, app_rsp[AppLc].error |->
          app_rsp[AppLc].digest_share0 == 0 && app_rsp[AppLc].digest_share1 == 0)

  `ASSERT(AppRomErrOutputZeros_A, app_rsp[AppRom].error |->
          app_rsp[AppRom].digest_share0 == 0 && app_rsp[AppRom].digest_share1 == 0)
endinterface
