// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has some assertions that check the inputs from ast react according to
// the pwrmgr outputs. The ast inputs are generated by the base sequences, but
// these assertions will also be useful at full chip level.
interface pwrmgr_ast_sva_if #(
  parameter bit CheckClocks = 1'b0
) (
  input logic                     clk_slow_i,
  input logic                     rst_slow_ni,
% for clk in src_clks:
  input logic                     clk_${clk}_i,
% endfor
  input logic                     por_d0_ni,
  // The pwrmgr outputs.
  input pwrmgr_pkg::pwr_ast_req_t pwr_ast_o,
  // The pwrmgr inputs.
  input pwrmgr_pkg::pwr_ast_rsp_t pwr_ast_i
);

  // These numbers of cycles are meant to match both the randomization in
  // pwrmgr_base_vseq, and the actual cycle counts from full chip.
  // Notice the expectation for full chip is that deassertion of *clk_val
  // takes 0 cycles, and assertion takes a 2 cycle synchronizer delay on
  // the slow clock; deassertion of main_pok takes one cycle, and assertion
  // not more than 2 cycles.
  localparam int MinClkWaitCycles = 0;
  localparam int MinPdnWaitCycles = 0;
  localparam int MaxClkWaitCycles = 60;
  localparam int MaxPdnWaitCycles = 110;

  bit disable_sva;
  bit reset_or_disable;

  always_comb reset_or_disable = !rst_slow_ni || disable_sva;

  `define CLK_WAIT_BOUNDS ##[MinClkWaitCycles:MaxClkWaitCycles]
  `define PDN_WAIT_BOUNDS ##[MinPdnWaitCycles:MaxPdnWaitCycles]

  // Clock enable-valid.

  // Changes triggered by por_d0_ni only affect clk_val.
<%
  # The cycle bounds are tuple (fall, rise)
  cycle_bounds = {clk: (5, 5) if clk == 'usb' else (1, 2) for clk in src_clks}
%>\
% for clk in src_clks:
<% ast_clk_name = 'core' if clk == 'main' else clk %>\
  `ASSERT(${clk.capitalize()}ClkGlitchToValOff_A, $fell(por_d0_ni) |-> ##[0:${cycle_bounds[clk][0]}] !pwr_ast_i.${ast_clk_name}_clk_val, clk_slow_i,
          reset_or_disable)
  `ASSERT(${clk.capitalize()}ClkGlitchToValOn_A,
          $rose(por_d0_ni) && pwr_ast_o.${ast_clk_name}_clk_en |-> ##[0:${cycle_bounds[clk][1]}] pwr_ast_i.${ast_clk_name}_clk_val, clk_slow_i,
          reset_or_disable)
% endfor
  // Changes not triggered by por_d0_ni
% for clk in src_clks:
<% ast_clk_name = 'core' if clk == 'main' else clk %>\
  % if clk == 'usb':
  // Usb is a bit different: apparently usb_clk_val can stay low after a power glitch, so it may
  // already be low when usb_clk_en drops.
  `ASSERT(UsbClkHandshakeOn_A,
          $rose(pwr_ast_o.usb_clk_en) && por_d0_ni && $past(por_d0_ni, 1) |-> `CLK_WAIT_BOUNDS
          pwr_ast_i.usb_clk_val || !por_d0_ni, clk_slow_i, reset_or_disable)
  `ASSERT(UsbClkHandshakeOff_A,
          $fell(pwr_ast_o.usb_clk_en) |-> `CLK_WAIT_BOUNDS !pwr_ast_i.usb_clk_val, clk_slow_i,
          reset_or_disable)
  % else:
  `ASSERT(${clk.capitalize()}ClkHandshakeOn_A,
          $rose(pwr_ast_o.${ast_clk_name}_clk_en) && por_d0_ni |-> `CLK_WAIT_BOUNDS
          pwr_ast_i.${ast_clk_name}_clk_val || !por_d0_ni, clk_slow_i, reset_or_disable)
  `ASSERT(${clk.capitalize()}ClkHandshakeOff_A,
          $fell(pwr_ast_o.${ast_clk_name}_clk_en) |-> `CLK_WAIT_BOUNDS !pwr_ast_i.${ast_clk_name}_clk_val, clk_slow_i,
          reset_or_disable)
  % endif

% endfor
  if (CheckClocks) begin : gen_check_clock
% for clk in src_clks:
    int ${clk}_clk_cycles;
    always_ff @(posedge clk_${clk}_i) ${clk}_clk_cyces++;
% endfor

% for clk in src_clks:
<% ast_clk_name = 'core' if clk == 'main' else clk %>\
    `ASSERT(${clk.capitalize() if clk == 'main' else clk.upper()}ClkStopped_A,
            $fell(
                pwr_ast_i.${ast_clk_name}_clk_val
            ) |=> ($stable(
                ${clk}_clk_cycles
            ) || pwr_ast_i.${ast_clk_name}_clk_val) [* 1 : $],
            clk_slow_i, reset_or_disable)
    `ASSERT(${clk.capitalize()}ClkRun_A,
            $rose(
                pwr_ast_i.${ast_clk_name}_clk_val
            ) |=> (!$stable(
                ${clk}_clk_cycles
            ) || !pwr_ast_i.${ast_clk_name}_clk_val) [* 1 : $],
            clk_slow_i, reset_or_disable)

% endfor
  end

  // Main pd-pok
  `ASSERT(MainPdHandshakeOn_A, pwr_ast_o.main_pd_n |-> `PDN_WAIT_BOUNDS pwr_ast_i.main_pok,
          clk_slow_i, reset_or_disable)
  `ASSERT(MainPdHandshakeOff_A, !pwr_ast_o.main_pd_n |-> `PDN_WAIT_BOUNDS !pwr_ast_i.main_pok,
          clk_slow_i, reset_or_disable)

  `undef CLK_WAIT_BOUNDS
  `undef PDN_WAIT_BOUNDS
endinterface
