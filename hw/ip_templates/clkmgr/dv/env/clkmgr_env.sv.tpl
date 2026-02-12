// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
from ipgen.clkmgr_gen import get_rg_srcs
all_src_names = sorted(s['name'] for s in src_clks.values())
rg_srcs = get_rg_srcs(typed_clocks)
%>\

class clkmgr_env extends cip_base_env #(
  .CFG_T              (clkmgr_env_cfg),
  .COV_T              (clkmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(clkmgr_virtual_sequencer),
  .SCOREBOARD_T       (clkmgr_scoreboard)
);
  `uvm_component_utils(clkmgr_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

% for src in all_src_names:
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "${src}_clk_rst_vif", cfg.${src}_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get ${src}_clk_rst_vif from uvm_config_db")
    end
% endfor
% for src in derived_clks.values():
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "${src['name']}_clk_rst_vif", cfg.${src['name']}_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get ${src['name']}_clk_rst_vif from uvm_config_db")
    end
% endfor
% for clk_family in parent_child_clks.values():
  % for src in clk_family:
    if (!uvm_config_db#(virtual clk_rst_if)::get(
            this, "", "root_${src}_clk_rst_vif", cfg.root_${src}_clk_rst_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get root_${src}_clk_rst_vif from uvm_config_db")
    end
  % endfor
% endfor

    if (!uvm_config_db#(virtual clkmgr_if)::get(this, "", "clkmgr_vif", cfg.clkmgr_vif)) begin
      `uvm_fatal(`gfn, "failed to get clkmgr_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual clkmgr_csrs_if)::get(
            this, "", "clkmgr_csrs_vif", cfg.clkmgr_csrs_vif
        )) begin
      `uvm_fatal(`gfn, "failed to get clkmgr_csrs_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
