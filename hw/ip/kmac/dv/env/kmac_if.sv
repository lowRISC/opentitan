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

  // EDN interface except the handshake to always complete.
  // But in KMAC, the handshake can be interrupted if there are terminal errors or reset.
  // So this function disable EDN related assertions.
  function automatic void disable_edn_asserts();
    `ifdef EN_MASKING
      $assertoff(0,
          dut.gen_entropy.u_prim_sync_reqack_data.u_prim_sync_reqack.SyncReqAckAckNeedsReq);
      $assertoff(0, edn_if[0].ReqHighUntilAck_A);
      $assertoff(0, edn_if[0].AckAssertedOnlyWhenReqAsserted_A);
    `endif
  endfunction

  // This assertion will not be true if keccak operation is interrupted by lc_escalate_en signal.
  function automatic void disable_keccak_asserts();
    `ifdef EN_MASKING
      $assertoff(0, dut.u_sha3.u_keccak.u_keccak_p.gen_selperiod_chk.SelStayTwoCycleIfTrue_A);
    `endif
  endfunction

  `ifdef EN_MASKING
    `ASSERT(KmacMaskingO_A, en_masking_o == 1)
  `else
    `ASSERT(KmacMaskingO_A, en_masking_o == 0)
  `endif

  `ASSERT(AppKeymgrErrOutputZeros_A, app_rsp[AppKeymgr].error |->
          app_rsp[AppKeymgr].digest_share0 == 0 && app_rsp[AppKeymgr].digest_share1 == 0)

  `ASSERT(AppLcErrOutputZeros_A, app_rsp[AppLc].error |->
          app_rsp[AppLc].digest_share0 == 0 && app_rsp[AppLc].digest_share1 == 0)

  `ASSERT(AppRomErrOutputZeros_A, app_rsp[AppRom].error |->
          app_rsp[AppRom].digest_share0 == 0 && app_rsp[AppRom].digest_share1 == 0)
endinterface
