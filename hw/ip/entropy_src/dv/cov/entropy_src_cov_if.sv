// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for entropy_src.
interface entropy_src_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import entropy_src_pkg::*;
  import entropy_src_env_pkg::*;
  `include "dv_fcov_macros.svh"

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  covergroup entropy_src_cfg_cg with function sample(prim_mubi_pkg::mubi4_t   route_software);
    option.name         = "entropy_src_cfg_cg";
    option.per_instance = 1;

    cp_route_software: coverpoint route_software;
  endgroup : entropy_src_cfg_cg

  `DV_FCOV_INSTANTIATE_CG(entropy_src_cfg_cg, en_full_cov)

  // Sample functions needed for xcelium
  function automatic void cg_cfg_sample(entropy_src_env_cfg cfg);
    entropy_src_cfg_cg_inst.sample(cfg.route_software);
  endfunction

endinterface : entropy_src_cov_if
