// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for OTP_CTRL

interface otp_ctrl_cov_if
  import otp_ctrl_reg_pkg::*;
  (
   input pwrmgr_pkg::pwr_otp_rsp_t                                 pwr_otp_o,
   input otp_ctrl_pkg::lc_otp_program_req_t                        lc_otp_program_i,
   input bit [3:0]                                                 lc_escalate_en_i,
   input otp_ctrl_pkg::flash_otp_key_req_t                         flash_otp_key_i,
   input otp_ctrl_pkg::sram_otp_key_req_t [NumSramKeyReqSlots-1:0] sram_otp_key_i,
   input otp_ctrl_pkg::otbn_otp_key_req_t                          otbn_otp_key_i
   );

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"

  covergroup lc_esc_en_condition_cg @(lc_escalate_en_i == lc_ctrl_pkg::On);
    lc_esc_during_flash_data_req:  coverpoint flash_otp_key_i.data_req;
    lc_esc_during_flash_addr_req:  coverpoint flash_otp_key_i.addr_req;
    lc_esc_during_sram_0_req:      coverpoint sram_otp_key_i[0].req;
    lc_esc_during_sram_1_req:      coverpoint sram_otp_key_i[1].req;
    lc_esc_during_otbn_req:        coverpoint otbn_otp_key_i.req;
    lc_esc_during_otp_idle:        coverpoint pwr_otp_o.otp_idle;
    lc_esc_during_lc_otp_prog_req: coverpoint lc_otp_program_i.req;
  endgroup

  covergroup flash_data_req_condition_cg @(flash_otp_key_i.data_req);
    flash_data_req_during_lc_esc: coverpoint lc_escalate_en_i {
      bins lc_esc_on  = {lc_ctrl_pkg::On};
      bins lc_esc_off = {[0 : lc_ctrl_pkg::On-1], [lc_ctrl_pkg::On+1 : '1]};
    }
    flash_data_req_during_flash_addr_req: coverpoint flash_otp_key_i.addr_req;
    flash_data_req_during_sram_0_req:     coverpoint sram_otp_key_i[0].req;
    flash_data_req_during_sram_1_req:     coverpoint sram_otp_key_i[1].req;
    flash_data_req_during_otbn_req:       coverpoint otbn_otp_key_i.req;
    flash_data_req_during_otp_idle:       coverpoint pwr_otp_o.otp_idle;
  endgroup

  covergroup flash_addr_req_condition_cg @(flash_otp_key_i.addr_req);
    flash_addr_req_during_lc_esc: coverpoint lc_escalate_en_i {
      bins lc_esc_on  = {lc_ctrl_pkg::On};
      bins lc_esc_off = {[0 : lc_ctrl_pkg::On-1], [lc_ctrl_pkg::On+1 : '1]};
    }
    flash_addr_req_during_flash_data_req: coverpoint flash_otp_key_i.data_req;
    flash_addr_req_during_sram_0_req:     coverpoint sram_otp_key_i[0].req;
    flash_addr_req_during_sram_1_req:     coverpoint sram_otp_key_i[1].req;
    flash_addr_req_during_otbn_req:       coverpoint otbn_otp_key_i.req;
    flash_addr_req_during_otp_idle:       coverpoint pwr_otp_o.otp_idle;
  endgroup

  covergroup sram_0_req_condition_cg @(sram_otp_key_i[0].req);
    sram_0_req_during_lc_esc: coverpoint lc_escalate_en_i {
      bins lc_esc_on  = {lc_ctrl_pkg::On};
      bins lc_esc_off = {[0 : lc_ctrl_pkg::On-1], [lc_ctrl_pkg::On+1 : '1]};
    }
    sram_0_req_during_flash_addr_req: coverpoint flash_otp_key_i.addr_req;
    sram_0_req_during_flash_data_req: coverpoint flash_otp_key_i.data_req;
    sram_0_req_during_sram_1_req:     coverpoint sram_otp_key_i[1].req;
    sram_0_req_during_otbn_req:       coverpoint otbn_otp_key_i.req;
    sram_0_req_during_otp_idle:       coverpoint pwr_otp_o.otp_idle;
  endgroup

  covergroup sram_1_req_condition_cg @(sram_otp_key_i[1].req);
    sram_1_req_during_lc_esc: coverpoint lc_escalate_en_i {
      bins lc_esc_on  = {lc_ctrl_pkg::On};
      bins lc_esc_off = {[0 : lc_ctrl_pkg::On-1], [lc_ctrl_pkg::On+1 : '1]};
    }
    sram_1_req_during_flash_addr_req: coverpoint flash_otp_key_i.addr_req;
    sram_1_req_during_flash_data_req: coverpoint flash_otp_key_i.data_req;
    sram_1_req_during_sram_0_req:     coverpoint sram_otp_key_i[0].req;
    sram_1_req_during_otbn_req:       coverpoint otbn_otp_key_i.req;
    sram_1_req_during_otp_idle:       coverpoint pwr_otp_o.otp_idle;
  endgroup

  covergroup otbn_req_condition_cg @(otbn_otp_key_i.req);
    otbn_req_during_lc_esc: coverpoint lc_escalate_en_i {
      bins lc_esc_on  = {lc_ctrl_pkg::On};
      bins lc_esc_off = {[0 : lc_ctrl_pkg::On-1], [lc_ctrl_pkg::On+1 : '1]};
    }
    otbn_req_during_flash_addr_req: coverpoint flash_otp_key_i.addr_req;
    otbn_req_during_flash_data_req: coverpoint flash_otp_key_i.data_req;
    otbn_req_during_sram_0_req:     coverpoint sram_otp_key_i[0].req;
    otbn_req_during_sram_1_req:     coverpoint sram_otp_key_i[1].req;
    otbn_req_during_otp_idle:       coverpoint pwr_otp_o.otp_idle;
  endgroup

  covergroup lc_prog_req_condition_cg @(lc_otp_program_i.req);
    lc_prog_req_during_lc_esc: coverpoint lc_escalate_en_i {
      bins lc_esc_on  = {lc_ctrl_pkg::On};
      bins lc_esc_off = {[0 : lc_ctrl_pkg::On-1], [lc_ctrl_pkg::On+1 : '1]};
    }
    lc_prog_req_during_flash_addr_req: coverpoint flash_otp_key_i.addr_req;
    lc_prog_req_during_flash_data_req: coverpoint flash_otp_key_i.data_req;
    lc_prog_req_during_sram_0_req:     coverpoint sram_otp_key_i[0].req;
    lc_prog_req_during_sram_1_req:     coverpoint sram_otp_key_i[1].req;
    lc_prog_req_during_otbn_req:       coverpoint otbn_otp_key_i.req;
    lc_prog_req_during_otp_idle:       coverpoint pwr_otp_o.otp_idle;
  endgroup

  `DV_FCOV_INSTANTIATE_CG(lc_esc_en_condition_cg)
  `DV_FCOV_INSTANTIATE_CG(flash_data_req_condition_cg)
  `DV_FCOV_INSTANTIATE_CG(flash_addr_req_condition_cg)
  `DV_FCOV_INSTANTIATE_CG(sram_0_req_condition_cg)
  `DV_FCOV_INSTANTIATE_CG(sram_1_req_condition_cg)
  `DV_FCOV_INSTANTIATE_CG(otbn_req_condition_cg)
  `DV_FCOV_INSTANTIATE_CG(lc_prog_req_condition_cg)

endinterface
