// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The indication checks of the single power-domain reset manager, for the resets that the secondary
// partition generates. rstmgr_bind binds this interface to rstmgr_part_secondary.
// rstmgr_rst_en_track_primary_sva_if has the checks of the resets that the primary partition
// generates.
<%
from topgen.lib import Name
from ipgen.manager_split import (rstmgr_clocks, rstmgr_hosted_domains, rstmgr_is_array,
                                 rstmgr_out_domains)
part = 'secondary'
part_clks = getattr(rstmgr_clocks(clk_freqs, leaf_rsts, rst_ni), part)

def sel(rst, domain):
  """Return the select of a power domain in this partition's struct field of a reset."""
  hosted = rstmgr_hosted_domains(rst, part)
  return f"[rstmgr_pkg::Domain{domain}Sel]" if rstmgr_is_array(hosted, power_domains) else ""

OUT = 'resets_secondary_o'

def rst_x(rst, n, domain):
  """Return the output field that a leaf of this partition drives, in the output's shape. Each copy
  of a reset (plain or shadowed) has its own output domains."""
  out = rstmgr_out_domains(rst, part, n)
  assert domain in out, (f"{rst['name']} [{domain}] is generated in the {part} partition but not "
                         f"output: these checks cannot see it")
  s = f"[rstmgr_pkg::Domain{domain}Sel]" if rstmgr_is_array(out, power_domains) else ""
  return f"{OUT}.rst_{n}_n{s}"

def en_x(rst, n, domain):
  """Return where the reset asserted indication of a leaf of this partition goes."""
  if part == 'primary':
    s = f"[rstmgr_pkg::Domain{domain}Sel]" if rstmgr_is_array(rst['domains'], power_domains) else ""
    return f"rst_en_o.{n}{s}"
  return f"intraip_s2p_o.rst_en_{n}_{domain.lower()}"
%>\

// This checks that the outgoing resets and the corresponding reset enable going to alert handler
// are shifted by a single clock cycle.
interface rstmgr_rst_en_track_secondary_sva_if (
% for clk in part_clks:
  input logic clk_${clk}_i,
% endfor
  input logic rst_por_ni,
  input rstmgr_pkg::rstmgr_out_secondary_t resets_secondary_o,
  input rstmgr_pkg::intraip_s2p_t intraip_s2p_o
);
  localparam int DELAY = 1;

% for rst in output_rsts:
<% rst_camel_name = Name.to_camel_case(rst['name']) %>\
  % for domain in rstmgr_hosted_domains(rst, part):
<% s = sel(rst, domain) %>\
    % if rst['shadowed']:
  `ASSERT(D${domain.capitalize()}Rst${rst_camel_name}ShadowedEnTracksRst${rst_camel_name}ShadowedActive_A,
          $fell(${rst_x(rst, rst['name'] + '_shadowed', domain)}) |-> ##[0:DELAY]
          ${en_x(rst, rst['name'] + '_shadowed', domain)} == prim_mubi_pkg::MuBi4True,
          clk_${rst['clock']}_i,
          !rst_por_ni)

  `ASSERT(D${domain.capitalize()}Rst${rst_camel_name}ShadowedEnTracksRst${rst_camel_name}ShadowedInactive_A,
          $rose(${rst_x(rst, rst['name'] + '_shadowed', domain)}) |-> ##DELAY
          !${rst_x(rst, rst['name'] + '_shadowed', domain)} ||
          ${en_x(rst, rst['name'] + '_shadowed', domain)} == prim_mubi_pkg::MuBi4False,
          clk_${rst['clock']}_i,
          !rst_por_ni)

    % else:
  `ASSERT(D${domain.capitalize()}Rst${rst_camel_name}EnTracksRst${rst_camel_name}Active_A,
          $fell(${rst_x(rst, rst['name'], domain)}) |-> ##[0:DELAY]
          ${en_x(rst, rst['name'], domain)} == prim_mubi_pkg::MuBi4True,
          clk_${rst['clock']}_i,
          !rst_por_ni)

  `ASSERT(D${domain.capitalize()}Rst${rst_camel_name}EnTracksRst${rst_camel_name}Inactive_A,
          $rose(${rst_x(rst, rst['name'], domain)}) |-> ##DELAY
          !${rst_x(rst, rst['name'], domain)} ||
          ${en_x(rst, rst['name'], domain)} == prim_mubi_pkg::MuBi4False,
          clk_${rst['clock']}_i,
          !rst_por_ni)

    % endif
  % endfor
% endfor
endinterface
