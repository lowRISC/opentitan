// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
from ipgen.clkmgr_gen import (config_clk_meas, get_all_srcs, get_hint_targets,
                              get_rg_srcs)
from topgen.lib import Name
rg_srcs = get_rg_srcs(typed_clocks)
all_srcs = get_all_srcs(src_clks, derived_clks)
clk_freqs = {v['name']: v['freq'] for v in all_srcs.values()}
hint_targets = get_hint_targets(typed_clocks)
%>
package clkmgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import sec_cm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import clkmgr_ral_pkg::*;
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  import lc_ctrl_pkg::lc_tx_t;
  import lc_ctrl_pkg::On;
  import lc_ctrl_pkg::Off;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  typedef virtual clkmgr_if clkmgr_vif;
  typedef virtual clk_rst_if clk_rst_vif;

  // parameters
  parameter int NUM_PERI = ${len(typed_clocks['sw_clks'])};
  parameter int NUM_TRANS = ${len(hint_names)};

  typedef logic [NUM_PERI-1:0] peri_enables_t;
  typedef logic [NUM_TRANS-1:0] hintables_t;
  typedef mubi4_t [NUM_TRANS-1:0] mubi_hintables_t;
  parameter mubi_hintables_t IdleAllBusy = {NUM_TRANS{prim_mubi_pkg::MuBi4False}};

% for clk, freq in clk_freqs.items():
  parameter int ${Name.to_camel_case(clk)}ClkHz = ${f"{freq:_}"};
% endfor
  parameter int FakeAonClkHz = 7_000_000;

  // alerts
  parameter uint NUM_ALERTS = 2;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {"recov_fault", "fatal_fault"};

  // types

  // Forward class decl to enable cfg to hold a scoreboard handle.
  typedef class clkmgr_scoreboard;

  // The enum values for these match the bit order in the CSRs.
  typedef enum int {
% for clk in typed_clocks['sw_clks'].values():
<% sep = "" if loop.last else "," %>\
    Peri${Name.to_camel_case(clk['src_name'])}${sep}
% endfor
  } peri_e;
  typedef struct packed {
% for clk in [c for c in reversed(typed_clocks['sw_clks'].values())]:
    logic ${clk['src_name']}_peri_en;
% endfor
  } clk_enables_t;

  typedef enum int {
% for target in hint_targets:
<% sep = "" if loop.last else "," %>\
    Trans${target.capitalize()}${sep}
% endfor
  } trans_e;
  typedef struct packed {
% for target in reversed(hint_targets):
    logic ${target};
% endfor
  } clk_hints_t;

  typedef struct {
    logic valid;
    logic slow;
    logic fast;
  } freq_measurement_t;

  // These are ordered per the bits in the recov_err_code register.
  typedef enum int {
% for src in rg_srcs:
    ClkMesr${Name.to_camel_case(src)},
% endfor
    ClkMesrSize
  } clk_mesr_e;

  // Mubi test mode
  typedef enum int {
    ClkmgrMubiNone   = 0,
    ClkmgrMubiIdle   = 1,
    ClkmgrMubiLcCtrl = 2,
    ClkmgrMubiLcHand = 3,
    ClkmgrMubiHand   = 4,
    ClkmgrMubiDiv    = 5
  } clkmgr_mubi_e;

  // This is to examine separately the measurement and timeout recoverable error bits.
  typedef logic [ClkMesrSize-1:0] recov_bits_t;

  typedef struct packed {
    recov_bits_t timeouts;
    recov_bits_t measures;
    logic shadow_update;
  } clkmgr_recov_err_t;

  // These must be after the declaration of clk_mesr_e for sizing.
  parameter int ClkInHz[ClkMesrSize] = {
% for src in rg_srcs:
<% sep = "" if loop.last else "," %>\
    ${Name.to_camel_case(src)}ClkHz${sep}
% endfor
  };

  // Take into account if multiple aon clock cycles are needed for a measurement.
  parameter int ExpectedCounts[ClkMesrSize] = {
% for src in rg_srcs:
<%
reference_cycles = config_clk_meas(src, all_srcs).reference_cycles
sep = "" if loop.last else ","
%>\
  % if reference_cycles == 1:
    ClkInHz[ClkMesr${Name.to_camel_case(src)}] / AonClkHz - 1${sep}
  % else:
    (ClkInHz[ClkMesr${Name.to_camel_case(src)}] / AonClkHz) * ${reference_cycles} - 1${sep}
  % endif
% endfor
  };

  // functions
  function automatic void print_hintable(hintables_t tbl);
    foreach (tbl[i]) begin
      `uvm_info("HINTBL", $sformatf("entry%0d : %b", i, tbl[i]), UVM_LOW)
    end
  endfunction : print_hintable

  function automatic void print_mubi_hintable(mubi_hintables_t tbl);
    string val = "INVALID";
    foreach (tbl[i]) begin
      if (tbl[i].name != "") val = tbl[i].name;
      `uvm_info("MUBIHINTBL", $sformatf("entry%0d : %s", i, val), UVM_LOW)
    end
  endfunction : print_mubi_hintable

  // package sources
  `include "clkmgr_env_cfg.sv"
  `include "clkmgr_env_cov.sv"
  `include "clkmgr_virtual_sequencer.sv"
  `include "clkmgr_scoreboard.sv"
  `include "clkmgr_env.sv"
  `include "clkmgr_vseq_list.sv"

endpackage
