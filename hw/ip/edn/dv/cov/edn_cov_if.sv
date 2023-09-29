// Copyright lowRISC contributors.
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

  covergroup edn_cs_cmds_cg with function sample(csrng_pkg::acmd_e acmd,
                                                 bit[3:0]  clen,
                                                 bit[3:0]  flags,
                                                 bit[18:0] glen
                                                );
    option.name         = "edn_cs_cmds_cg";
    option.per_instance = 1;

    cp_acmd: coverpoint acmd {
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

    // for generate cmds, clen & glen matter
    cr_acmd_clen_glen: cross cp_acmd, cp_clen, cp_glen {
      ignore_bins glen_not_used_cross = ! binsof(cp_acmd) intersect { csrng_pkg::GEN };
    }

    // for instantiate and reseed cmds, clen & flag0 matter
    cr_acmd_clen_flags: cross cp_acmd, cp_clen, cp_flags {
      ignore_bins flag0_not_used_cross =
          ! binsof(cp_acmd) intersect { csrng_pkg::INS, csrng_pkg::RES };
    }

    // for update cmds, only clen matters
    cr_acmd_clen: cross cp_acmd, cp_clen {
      ignore_bins non_upd_cross = ! binsof(cp_acmd) intersect { csrng_pkg::UPD };
    }

    // for uninstantiate cmds, nothing else matters
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

  `DV_FCOV_INSTANTIATE_CG(edn_cfg_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_endpoints_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_cs_cmds_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_error_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_alert_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_cfg_sample(edn_env_cfg cfg);
    edn_cfg_cg_inst.sample(cfg.num_endpoints,
                           cfg.num_boot_reqs,
                           cfg.boot_req_mode,
                           cfg.auto_req_mode);
  endfunction

  function automatic void cg_cs_cmds_sample(csrng_pkg::acmd_e acmd, bit[3:0] clen, bit[3:0] flags, bit[18:0] glen);
    edn_cs_cmds_cg_inst.sample(acmd, clen, flags, glen);
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

endinterface : edn_cov_if
