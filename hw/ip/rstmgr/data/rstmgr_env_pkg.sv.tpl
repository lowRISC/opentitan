// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gen_sv_comment}

package rstmgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import rstmgr_ral_pkg::*;

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  import rstmgr_reg_pkg::NumHwResets;
  import rstmgr_reg_pkg::NumSwResets;

  import alert_pkg::alert_crashdump_t;
  import rv_core_ibex_pkg::cpu_crash_dump_t;

  import sec_cm_pkg::*;
  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"fatal_fault", "fatal_cnsty_fault"};
  parameter uint NUM_ALERTS = 2;

  parameter string LIST_OF_LEAFS[] = {
<%
  list_of_leafs = []
  for rst in leaf_rsts:
    if rst.name != rst_ni:
      for domain in rst.domains:
        list_of_leafs.append(f"u_d{domain.lower()}_{rst.name}")
        if rst.shadowed:
          list_of_leafs.append(f"u_d{domain.lower()}_{rst.name}_shadowed")
%>\
% for leaf in list_of_leafs:
    "${leaf}"${"" if loop.last else ","}
% endfor
  };

  // Instances of rstmgr_leaf_rst modules which have a shadow pair.
  parameter string LIST_OF_SHADOW_LEAFS[] = {
<%
  list_of_shadowed_leafs = []
  for rst in leaf_rsts:
    if rst.shadowed:
      for domain in rst.domains:
        list_of_shadowed_leafs.append(
            f"u_d{domain.lower()}_{rst.name}")
%>\
% for shadowed_leaf in list_of_shadowed_leafs:
    "${shadowed_leaf}"${"" if loop.last else ","}
% endfor
  };

  // types
  typedef logic [NumSwResets-1:0] sw_rst_t;
  typedef class rstmgr_scoreboard;

  typedef logic [$bits(alert_crashdump_t)-1:0] linearized_alert_dump_t;

  // functions

  // package sources
  `include "rstmgr_env_cfg.sv"
  `include "rstmgr_env_cov.sv"
  `include "rstmgr_virtual_sequencer.sv"
  `include "rstmgr_scoreboard.sv"
  `include "rstmgr_env.sv"
  `include "rstmgr_vseq_list.sv"

endpackage
