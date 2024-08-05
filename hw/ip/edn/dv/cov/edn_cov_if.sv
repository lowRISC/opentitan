// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for edn.
interface edn_cov_if (
  input logic                                          clk_i,
  input logic [edn_env_pkg::MAX_NUM_ENDPOINTS - 1:0]   ep_req
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import edn_pkg::*;
  import csrng_agent_pkg::*;
  import edn_env_pkg::*;
  import prim_mubi_pkg::*;
  `include "dv_fcov_macros.svh"

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;
  bit [MAX_NUM_ENDPOINTS - 1:0]   ep_requests;

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  assign ep_requests = {ep_req[6], ep_req[5], ep_req[4], ep_req[3],
                        ep_req[2], ep_req[1], ep_req[0]};

  covergroup edn_cfg_cg with function sample(bit [2:0] num_endpoints,
                                             uint      num_boot_reqs,
                                             mubi4_t   boot_req_mode,
                                             mubi4_t   auto_req_mode);
    option.name         = "edn_cfg_cg";
    option.per_instance = 1;

    cp_num_endpoints: coverpoint num_endpoints {
      ignore_bins zero = { 0 };
    }
    cp_num_boot_reqs: coverpoint num_boot_reqs {
      bins         single   = { 1 };
      bins         multiple = { [2:$] };
      ignore_bins  zero     = { 0 };
    }
    cp_mode: coverpoint {boot_req_mode, auto_req_mode} {
      bins         sw_mode       = { {MuBi4False, MuBi4False} };
      bins         auto_req_mode = { {MuBi4False, MuBi4True} };
      bins         boot_req_mode = { {MuBi4True, MuBi4False} };
      illegal_bins both          = { {MuBi4True, MuBi4True} };
    }

    cr_num_endpoints_mode: cross cp_num_endpoints, cp_mode;
  endgroup : edn_cfg_cg

  covergroup edn_endpoints_cg @(ep_requests);
    option.name         = "edn_endpoints_cg";
    option.per_instance = 1;

    cp_ep_requests: coverpoint ep_requests {
      bins none = { $countones(ep_requests) == 0 };
      bins some = { $countones(ep_requests) inside { [1:MAX_NUM_ENDPOINTS - 1] } };
      bins all  = { $countones(ep_requests) == MAX_NUM_ENDPOINTS };
    }
  endgroup : edn_endpoints_cg

  covergroup edn_cs_cmds_cg with function sample(bit[3:0]                   clen,
                                                 bit[3:0]                   flags,
                                                 bit[18:0]                  glen,
                                                 csrng_pkg::acmd_e          acmd,
                                                 edn_env_pkg::cmd_type_e    cmd_src,
                                                 edn_env_pkg::hw_req_mode_e mode
                                                );
    option.name         = "edn_cs_cmds_cg";
    option.per_instance = 1;

    cp_acmd: coverpoint acmd {
      // ignore unused/invalid commands
      ignore_bins unused = { csrng_pkg::GENB, csrng_pkg::GENU, csrng_pkg::INV };
    }

    cp_clen: coverpoint clen {
      bins no_cmd_data   = { 0 };
      bins some_cmd_data = { [1:$] };
    }

    cp_flags: coverpoint flags {
      bins false         = { MuBi4False };
      bins true          = { MuBi4True };
    }

    cp_glen: coverpoint glen {
      bins one         = { 1 };
      bins multiple    = { [2:$] };
      ignore_bins zero = { 0 };
    }

    cp_mode: coverpoint mode {
      bins auto_mode = { edn_env_pkg::AutoReqMode };
      bins boot_mode = { edn_env_pkg::BootReqMode };
      bins sw_mode   = { edn_env_pkg::SwMode };
    }

    cp_cmd_src: coverpoint cmd_src {
      bins boot_ins_cmd = { edn_env_pkg::BootIns };
      bins boot_gen_cmd = { edn_env_pkg::BootGen };
      bins generate_cmd = { edn_env_pkg::AutoGen };
      bins reseed_cmd   = { edn_env_pkg::AutoRes };
      bins sw_cmd_req   = { edn_env_pkg::Sw };
    }

    // We want to see generate commands with every type of cp clen and glen
    // in every intended mode and register
    cr_generate_intended: cross cp_acmd, cp_clen, cp_glen, cp_mode, cp_cmd_src {
      // Ignore non generate commands
      ignore_bins not_gen = ! binsof(cp_acmd) intersect { csrng_pkg::GEN };
      // Generate commands in auto mode that aren't from the generate register aren't intended
      ignore_bins gen_auto_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::AutoReqMode } &&
                                       ! binsof(cp_cmd_src) intersect { edn_env_pkg::AutoGen };
      // Generate commands in boot mode that aren't from the bootgen register aren't intended
      ignore_bins gen_boot_wrong_src =
          binsof(cp_mode) intersect { edn_env_pkg::BootReqMode } &&
          ! binsof(cp_cmd_src) intersect { edn_env_pkg::BootGen };
      // Generate commands in boot mode that have a clen > 0 aren't intended
      ignore_bins gen_boot_seq_wrong_clen =
          binsof(cp_mode) intersect { edn_env_pkg::BootReqMode } &&
          binsof(cp_cmd_src) intersect { edn_env_pkg::BootGen } &&
          ! binsof(cp_clen) intersect { 0 };
      // Generate commands in boot mode that have a glen of multiple words aren't intended
      ignore_bins gen_boot_seq_wrong_glen =
          binsof(cp_mode) intersect { edn_env_pkg::BootReqMode } &&
          binsof(cp_cmd_src) intersect { edn_env_pkg::BootGen } &&
          ! binsof(cp_glen) intersect { [2:$] };
      // Generate commands in sw mode that aren't from the sw register aren't intended
      ignore_bins gen_sw_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::SwMode } &&
                                     ! binsof(cp_cmd_src) intersect { edn_env_pkg::Sw };
    }

    // We want to see instantiate commands with every type of cp clen and flag0
    // in every intended mode and register
    cr_instantiate_intended: cross cp_acmd, cp_clen, cp_flags, cp_mode, cp_cmd_src {
      // Ignore non instantiate commands
      ignore_bins not_ins = ! binsof(cp_acmd) intersect { csrng_pkg::INS };
      // Instantiate commands in auto mode that aren't from the Sw register aren't intended
      ignore_bins ins_auto_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::AutoReqMode } &&
                                       ! binsof(cp_cmd_src) intersect { edn_env_pkg::Sw };
      // Instantiate commands in boot mode that aren't from the BootIns register aren't intended
      ignore_bins ins_boot_wrong_src =
          binsof(cp_mode) intersect { edn_env_pkg::BootReqMode } &&
          ! binsof(cp_cmd_src) intersect { edn_env_pkg::BootIns };
      // Instantiate commands in boot mode that have a clen > 0 aren't intended
      ignore_bins ins_boot_seq_wrong_clen =
          binsof(cp_mode) intersect { edn_env_pkg::BootReqMode } &&
          binsof(cp_cmd_src) intersect { edn_env_pkg::BootIns } &&
          ! binsof(cp_clen) intersect { 0 };
      // Instantiate commands in boot mode that have a flag0 = MuBi4True aren't intended
      ignore_bins ins_boot_seq_wrong_flag0 =
          binsof(cp_mode) intersect { edn_env_pkg::BootReqMode } &&
          binsof(cp_cmd_src) intersect { edn_env_pkg::BootIns } &&
          ! binsof(cp_flags) intersect { MuBi4False };
      // Instantiate commands in sw mode that aren't from the sw register aren't intended
      ignore_bins ins_sw_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::SwMode } &&
                                     ! binsof(cp_cmd_src) intersect { edn_env_pkg::Sw };
    }

    // We want to see reseed commands with every type of cp clen and flag0
    // in every intended mode and register
    cr_reseed_intended: cross cp_acmd, cp_clen, cp_flags, cp_mode, cp_cmd_src {
      // Ignore non reseed commands
      ignore_bins not_res = ! binsof(cp_acmd) intersect { csrng_pkg::RES };
      // Reseed commands in auto mode that aren't from the autoRes register aren't intended
      ignore_bins res_auto_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::AutoReqMode } &&
                                       ! binsof(cp_cmd_src) intersect { edn_env_pkg::AutoRes };
      // Reseed commands in boot mode aren't intended
      ignore_bins res_boot_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::BootReqMode };
      // Reseed commands in sw mode that aren't from the sw register aren't intended
      ignore_bins res_sw_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::SwMode } &&
                                     ! binsof(cp_cmd_src) intersect { edn_env_pkg::Sw };
    }

    // We want to see update commands with every type of cp clen
    // in every intended mode and register
    cr_update_intended: cross cp_acmd, cp_clen, cp_mode, cp_cmd_src {
      // Ignore non update commands
      ignore_bins not_upd = ! binsof(cp_acmd) intersect { csrng_pkg::UPD };
      // Update commands in auto mode aren't intended
      ignore_bins upd_auto_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::AutoReqMode };
      // Update commands in boot mode aren't intended
      ignore_bins upd_boot_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::BootReqMode };
      // Update commands in sw mode that aren't from the sw register aren't intended
      ignore_bins upd_sw_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::SwMode } &&
                                     ! binsof(cp_cmd_src) intersect { edn_env_pkg::Sw };
    }

    // We want to see uninstantiate commands in every intended mode and register
    cr_uninstantiate_intended: cross cp_acmd, cp_mode, cp_cmd_src {
      // Ignore non uninstantiate commands
      ignore_bins not_uni = ! binsof(cp_acmd) intersect { csrng_pkg::UNI };
      // Uninstantiate commands in auto mode aren't intended
      ignore_bins uni_auto_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::AutoReqMode };
      // Uninstantiate commands in boot mode are always the same.
      ignore_bins uni_boot_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::BootReqMode };
      // Uninstantiate commands in sw mode that aren't from the sw register aren't intended
      ignore_bins uni_sw_wrong_src = binsof(cp_mode) intersect { edn_env_pkg::SwMode } &&
                                     ! binsof(cp_cmd_src) intersect { edn_env_pkg::Sw };
    }

    // We want to see some unintended commands in every mode
    cr_acmd_mode_cmd_src_unintended: cross cp_acmd, cp_mode, cp_cmd_src {
      // Sw commands in auto mode aren't intended
      // Except for the initial instantiate at the start of auto mode
      ignore_bins not_sw_cmd = ! binsof(cp_mode) intersect { edn_env_pkg::AutoReqMode };
      ignore_bins not_auto_mode = ! binsof(cp_cmd_src) intersect { edn_env_pkg::Sw };
    }
  endgroup : edn_cs_cmds_cg

  covergroup edn_error_cg with function sample(err_code_test_e err_test);
    option.name         = "edn_error_cg";
    option.per_instance = 1;

    cp_error_test: coverpoint err_test;
  endgroup : edn_error_cg

  covergroup edn_alert_cg with function sample(recov_alert_bit_e recov_alert);
    option.name         = "edn_alert_cg";
    option.per_instance = 1;

    cp_recov_alert_cg: coverpoint recov_alert;
  endgroup : edn_alert_cg

  covergroup edn_cs_cmd_response_cg with function sample(bit csrng_rsp_sts);
    option.name         = "edn_cs_cmd_response_cg";
    option.per_instance = 1;

    cp_csrng_rsp_sts_cg: coverpoint csrng_rsp_sts {
      bins error   = { 1'b1 };
      bins success = { 1'b0 };
    }
  endgroup : edn_cs_cmd_response_cg

  covergroup edn_sw_cmd_sts_cg with function sample(bit cmd_rdy, bit cmd_reg_rdy,
                                                    csrng_pkg::csrng_cmd_sts_e cmd_sts,
                                                    bit cmd_ack);
    option.name         = "edn_sw_cmd_sts_cg";
    option.per_instance = 1;

    cp_cmd_rdy_cg: coverpoint cmd_rdy {
      bins ready     = { 1'b1 };
      bins not_ready = { 1'b0 };
    }

    cp_cmd_reg_rdy_cg: coverpoint cmd_reg_rdy {
      bins ready     = { 1'b1 };
      bins not_ready = { 1'b0 };
    }

    cp_cmd_sts_cg: coverpoint cmd_sts;

    cp_cmd_ack_cg: coverpoint cmd_ack {
      bins ack    = { 1'b1 };
      bins no_ack = { 1'b0 };
    }
  endgroup : edn_sw_cmd_sts_cg

  covergroup edn_hw_cmd_sts_cg with function sample(bit boot_mode, bit auto_mode,
                                                    csrng_pkg::csrng_cmd_sts_e cmd_sts,
                                                    bit cmd_ack, csrng_pkg::acmd_e acmd);
    option.name         = "edn_hw_cmd_sts_cg";
    option.per_instance = 1;

    cp_boot_mode: coverpoint boot_mode {
      bins boot_mode     = { 1'b1 };
      bins not_boot_mode = { 1'b0 };
    }

    cp_auto_mode: coverpoint auto_mode {
      bins auto_mode     = { 1'b1 };
      bins not_auto_mode = { 1'b0 };
    }

    cp_cmd_sts: coverpoint cmd_sts;

    cp_cmd_ack: coverpoint cmd_ack {
      bins ack    = { 1'b1 };
      bins no_ack = { 1'b0 };
    }

    cp_acmd: coverpoint acmd {
      // Ignore unused/invalid HW commands.
      ignore_bins unused = { csrng_pkg::GENB, csrng_pkg::GENU, csrng_pkg::INV, csrng_pkg::UPD };
    }

    // We want to see all of the boot commands in boot mode.
    cr_acmd_boot_mode: cross cp_acmd, cp_boot_mode {
      ignore_bins not_boot_mode = ! binsof(cp_boot_mode) intersect { 1'b1 };
      ignore_bins not_valid_boot_commands = ! binsof(cp_acmd) intersect { csrng_pkg::INS,
                                                                          csrng_pkg::GEN,
                                                                          csrng_pkg::UNI };
    }

    // We want to see all of the HW controlled auto mode commands in auto mode.
    cr_acmd_auto_mode: cross cp_acmd, cp_auto_mode {
      ignore_bins not_auto_mode = ! binsof(cp_auto_mode) intersect { 1'b1 };
      ignore_bins not_valid_boot_commands = ! binsof(cp_acmd) intersect { csrng_pkg::RES,
                                                                          csrng_pkg::GEN };
    }
  endgroup : edn_hw_cmd_sts_cg

  covergroup edn_endpoint_err_req_cg with function sample(uint endpoint);
    option.name         = "edn_endpoint_err_req_cg";
    option.per_instance = 1;

    // Create one bin per endpoint of EDN.
    endpoint_cg: coverpoint endpoint {
      bins range[MAX_NUM_ENDPOINTS] = {[0:MAX_NUM_ENDPOINTS-1]};
    }
  endgroup : edn_endpoint_err_req_cg

  `DV_FCOV_INSTANTIATE_CG(edn_cfg_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_endpoints_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_cs_cmds_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_error_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_alert_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_cs_cmd_response_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_sw_cmd_sts_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_hw_cmd_sts_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_endpoint_err_req_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_cfg_sample(edn_env_cfg cfg);
    edn_cfg_cg_inst.sample(cfg.num_endpoints,
                           cfg.num_boot_reqs,
                           cfg.boot_req_mode,
                           cfg.auto_req_mode);
  endfunction

  function automatic void cg_cs_cmds_sample(csrng_pkg::acmd_e acmd, bit[3:0] clen, bit[3:0] flags,
                                            bit[18:0] glen, edn_env_pkg::hw_req_mode_e mode,
                                            edn_env_pkg::cmd_type_e cmd_src);
    edn_cs_cmds_cg_inst.sample(clen, flags, glen, acmd, cmd_src, mode);
  endfunction

  function automatic void cg_error_sample(bit[31:0] err_code);
    err_code_test_e enum_val;
    enum_val = enum_val.first();
    forever begin
      if(err_code[enum_val]) begin
        edn_error_cg_inst.sample(enum_val);
      end
      if (enum_val == enum_val.last) begin
        break;
      end
      enum_val = enum_val.next();
    end
  endfunction : cg_error_sample

  function automatic void cg_alert_sample(bit[31:0] recov_alert_sts);
    recov_alert_bit_e enum_val;
    enum_val = enum_val.first();
    forever begin
      if(recov_alert_sts[enum_val]) begin
        edn_alert_cg_inst.sample(enum_val);
      end
      if (enum_val == enum_val.last) begin
        break;
      end
      enum_val = enum_val.next();
    end
  endfunction : cg_alert_sample

  function automatic void cg_cs_cmd_response_sample(bit csrng_rsp_sts, bit csrng_rsp_ack);
    if (csrng_rsp_ack) begin
      edn_cs_cmd_response_cg_inst.sample(csrng_rsp_sts);
    end
  endfunction : cg_cs_cmd_response_sample

  function automatic void cg_edn_sw_cmd_sts_sample(bit cmd_rdy, bit cmd_reg_rdy,
                                                   csrng_pkg::csrng_cmd_sts_e cmd_sts,
                                                   bit cmd_ack);
    edn_sw_cmd_sts_cg_inst.sample(cmd_rdy, cmd_reg_rdy, cmd_sts, cmd_ack);
  endfunction : cg_edn_sw_cmd_sts_sample

  function automatic void cg_edn_hw_cmd_sts_sample(bit boot_mode, bit auto_mode,
                                                   csrng_pkg::csrng_cmd_sts_e cmd_sts,
                                                   bit cmd_ack, csrng_pkg::acmd_e acmd);
    edn_hw_cmd_sts_cg_inst.sample(boot_mode, auto_mode, cmd_sts, cmd_ack, acmd);
  endfunction : cg_edn_hw_cmd_sts_sample

  function automatic void cg_edn_endpoint_err_req_sample(uint endpoint);
    edn_endpoint_err_req_cg_inst.sample(endpoint);
  endfunction : cg_edn_endpoint_err_req_sample

endinterface : edn_cov_if
