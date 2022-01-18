// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for edn.
interface edn_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import edn_pkg::*;
  import csrng_agent_pkg::*;
  import edn_env_pkg::*;
  `include "dv_fcov_macros.svh"

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  covergroup edn_cfg_cg with function sample(uint num_endpoints);
    option.name         = "edn_cfg_cg";
    option.per_instance = 1;

    cp_num_endpoints: coverpoint num_endpoints;
  endgroup : edn_cfg_cg

  `DV_FCOV_INSTANTIATE_CG(edn_cfg_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_cfg_sample(edn_env_cfg cfg);
    edn_cfg_cg_inst.sample(cfg.num_endpoints);
  endfunction

endinterface : edn_cov_if
