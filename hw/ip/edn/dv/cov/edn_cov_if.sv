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
                                             uint num_boot_reqs,
                                             bit  boot_req_mode,
                                             bit  auto_req_mode);
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

  covergroup edn_cs_cmds_cg with function sample(bit[3:0]    clen,
                                                 bit[3:0]    flags,
                                                 bit[18:0]   glen
                                                );
    option.name         = "edn_cs_cmds_cg";
    option.per_instance = 1;

    cp_clen: coverpoint clen {
      bins no_cmd_data   = { 0 };
      bins some_cmd_data = { [1:$] };
    }

    cp_flags: coverpoint flags {
      bins zero         = { 0 };
      bins one          = { 1 };
      ignore_bins other = { [2:$] };
    }

    cp_glen: coverpoint glen {
      bins one         = { 1 };
      bins multiple    = { [2:$] };
      ignore_bins zero = { 0 };
    }

    cr_clen_flags_glen:   cross cp_clen, cp_flags, cp_glen;
  endgroup : edn_cs_cmds_cg

  `DV_FCOV_INSTANTIATE_CG(edn_cfg_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_endpoints_cg, en_full_cov)
  `DV_FCOV_INSTANTIATE_CG(edn_cs_cmds_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_cfg_sample(edn_env_cfg cfg);
    edn_cfg_cg_inst.sample(cfg.num_endpoints,
                           cfg.num_boot_reqs,
                           cfg.boot_req_mode,
                           cfg.auto_req_mode);
  endfunction

  function automatic void cg_cs_cmds_sample(bit[3:0] clen, bit[3:0] flags, bit[18:0] glen);
    edn_cs_cmds_cg_inst.sample(clen,
                               flags,
                               glen);
  endfunction

endinterface : edn_cov_if
