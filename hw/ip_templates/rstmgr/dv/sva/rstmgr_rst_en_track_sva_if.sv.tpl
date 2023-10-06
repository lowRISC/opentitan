// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
from topgen.lib import Name
%>\

// This checks that the outgoing resets and the corresponding reset enable going to alert handler
// are shifted by a single clock cycle.
interface rstmgr_rst_en_track_sva_if (
  input rstmgr_pkg::rstmgr_out_t resets_i,
  input rstmgr_pkg::rstmgr_rst_en_t reset_en_i,
% for clk in clks:
  input logic clk_${clk}_i,
% endfor
  input logic rst_por_ni
);
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;
  localparam int DELAY = 1;

% for rst in output_rsts:
<%
  rst_name = Name.from_snake_case(rst.name)
  rst_camel_name = rst_name.as_camel_case()
%>\
  % for domain in rst.domains:
    % if rst.shadowed:
  `ASSERT(D${domain.capitalize()}Rst${rst_camel_name}ShadowedEnTracksRst${rst_camel_name}ShadowedActive_A,
          $fell(resets_i.rst_${rst.name}_shadowed_n[Domain${domain}Sel]) |-> ##[0:DELAY]
          reset_en_i.${rst.name}_shadowed[Domain${domain}Sel] == prim_mubi_pkg::MuBi4True,
          clk_${rst.clock.name}_i,
          !rst_por_ni)

  `ASSERT(D${domain.capitalize()}Rst${rst_camel_name}ShadowedEnTracksRst${rst_camel_name}ShadowedInactive_A,
          $rose(resets_i.rst_${rst.name}_shadowed_n[Domain${domain}Sel]) |-> ##DELAY
          !resets_i.rst_${rst.name}_shadowed_n[Domain${domain}Sel] ||
          reset_en_i.${rst.name}_shadowed[Domain${domain}Sel] == prim_mubi_pkg::MuBi4False,
          clk_${rst.clock.name}_i,
          !rst_por_ni)

    % else:
  `ASSERT(D${domain.capitalize()}Rst${rst_camel_name}EnTracksRst${rst_camel_name}Active_A,
          $fell(resets_i.rst_${rst.name}_n[Domain${domain}Sel]) |-> ##[0:DELAY]
          reset_en_i.${rst.name}[Domain${domain}Sel] == prim_mubi_pkg::MuBi4True,
          clk_${rst.clock.name}_i,
          !rst_por_ni)

  `ASSERT(D${domain.capitalize()}Rst${rst_camel_name}EnTracksRst${rst_camel_name}Inactive_A,
          $rose(resets_i.rst_${rst.name}_n[Domain${domain}Sel]) |-> ##DELAY
          !resets_i.rst_${rst.name}_n[Domain${domain}Sel] ||
          reset_en_i.${rst.name}[Domain${domain}Sel] == prim_mubi_pkg::MuBi4False,
          clk_${rst.clock.name}_i,
          !rst_por_ni)

    % endif
  % endfor
% endfor
endinterface
