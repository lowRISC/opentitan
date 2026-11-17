// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The cascading checks of the single power-domain reset manager, for the resets that the secondary
// partition generates. rstmgr_bind binds this interface to rstmgr_part_secondary.
// rstmgr_cascading_primary_sva_if has the checks of the resets that the primary partition
// generates.
<%
from topgen.lib import Name
from ipgen.manager_split import (rstmgr_clocks, rstmgr_hosted_domains, rstmgr_is_array,
                                 rstmgr_out_domains, rstmgr_routed_roots)
part = 'secondary'
part_clks = getattr(rstmgr_clocks(clk_freqs, leaf_rsts, rst_ni), part)
sorted_clks = sorted(clk_freqs.keys())
preferred = "io_div4" if "io_div4" in sorted_clks else "io"
rsts = {r['name']: r for r in output_rsts}

# The leaf resets that the cascading checks cover, with their power domain and edge bounds, as in
# the single power-domain reset manager: (assertion name, reset, shadowed, power domain, bounds).
# The reset tree gives the parent of each.
links = [("CascadeLcToLcAon", "lc_aon", False, "Aon", "SysCycles"),
         ("CascadeLcToLc", "lc", False, "Main", "SysCycles"),
         ("CascadeLcToLcShadowed", "lc", True, "Main", "SysCycles"),
         ("CascadeSysToSys", "sys", False, "Main", "PeriCycles"),
         ("CascadeSysToSysIoDiv4", f"sys_{preferred}", False, "Aon", "SysCycles"),
         ("CascadeEffAonToRstPorIoDiv4", f"por_{preferred}", False, "Aon", "SyncCycles")]
links += [(f"CascadeEffAonToRstPor{clk.capitalize()}", "por" if clk == "main" else f"por_{clk}",
           False, "Aon", "SyncCycles")
          for clk in sorted_clks if "aon" not in clk and "io_div4" not in clk]
# Keep the links whose reset this partition generates. A top without the reset has no link for it.
links = [(n, r, s, d, b) for n, r, s, d, b in links
         if r in rsts and d in rsts[r]['domains'] and (rsts[r]['shadowed'] or not s) and
         d in rstmgr_hosted_domains(rsts[r], part)]
OUT = 'resets_secondary_o'

def rst_x(rst, n, domain):
  """Return the output field that a leaf of this partition drives, in the output's shape. Each copy
  of a reset (plain or shadowed) has its own output domains."""
  out = rstmgr_out_domains(rst, part, n)
  assert domain in out, (f"{rst['name']} [{domain}] is generated in the {part} partition but not "
                         f"output: these checks cannot see it")
  s = f"[rstmgr_pkg::Domain{domain}Sel]" if rstmgr_is_array(out, power_domains) else ""
  return f"{OUT}.rst_{n}_n{s}"

%>\
// This has assertions that check the reset outputs of rstmgr cascade properly.
// This means higher level resets always cause the lower level ones to assert.
// The hierarchy is
//   por > lc > sys > specific peripherals
// In addition, a scan reset is at the same level as por.
//
// Local terminology: A cascading relationship is between an "above" and a "below" reset.
//
// Some individual reset outputs will always be off. Allowing for this in general would
// weaken the property that some resets MUST rise following other rise.
//
// Peripheral resets cascade from sys, and are checked in rstmgr_sw_rst_sva_if since they
// require additional inputs.
interface rstmgr_cascading_secondary_sva_if (
  input logic clk_i,
% for clk in part_clks:
  input logic clk_${clk}_i,
% endfor
  input [rstmgr_pkg::PowerDomains-1:0] por_n_i,
  input pwrmgr_pkg::pwr_rst_req_t pwr_i,
  input pwrmgr_pkg::pwr_rst_rsp_t pwr_o,
  input logic scan_rst_ni,
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input rstmgr_pkg::rstmgr_out_secondary_t resets_secondary_o,
  input [rstmgr_pkg::PowerDomains-1:0] rst_por_aon_n
);
  // The min and max bounds on the number of cycles for an edge to occur.
  typedef struct {
    int min;
    int max;
  } bounds_t;

  // The bounds for a fall and rise edge to occur.
  typedef struct {
    bounds_t fall;
    bounds_t rise;
  } edge_bounds_t;

  // This is used to check por_n_i active high leads to a rising edge of rst_por_aon_n[0].
  // The number of cycles with por_n_i stable is 32 plus synchronizers and some filter stages.
  localparam edge_bounds_t PorCycles = '{fall: '{min: 0, max: 4}, rise: '{min: 35, max: 40}};

  // This is used to check for regular synchronizing delay. Reset falls asynchronously so the
  // fall min cycles is zero.
  localparam edge_bounds_t SyncCycles = '{fall: '{min: 0, max: 3}, rise: '{min: 1, max: 3}};

  // Cycles are counted from the output rst_por_aon_n or scan reset edges. The rise times can be
  // higher since in the chip the aon reset goes through the pwrmgr slow fsm where it causes an
  // lc rise request and there may be multiple synchronizers in the path.
  localparam edge_bounds_t LcCycles = '{fall: '{min: 0, max: 4}, rise: '{min: 1, max: 4}};

  // In the real system the rise of rst_lc_src_n is triggered by the pwr_i.rst_lc_req input,
  // which can take a few cycles since it comes from the pwrmgr after it gets reset,
  // is generated with the aon clock, and gets synchronized before it triggers
  // a rise in rst_lc_src_n. There is an SVA for the rise in pwrmgr_rstmgr_sva_if.

  // The cycles are counted from Lc edges.
  localparam edge_bounds_t SysCycles = '{fall: '{min: 0, max: 3}, rise: '{min: 1, max: 5}};

  // The different peripheral edges are synchronized to their respective clocks,
  // so these counts assume synchronization and are triggered on the correct clock.
  localparam edge_bounds_t PeriCycles = '{fall: '{min: 0, max: 4}, rise: '{min: 2, max: 8}};

  bit disable_sva;

  // Macros to avoid excessive boiler-plate code below.
  `define FALL_ASSERT(_name, _from, _to, _cycles, _clk) ${"\\"}
    `ASSERT(_name``AboveFall_A, ${"\\"}
            $fell(_from) |-> ##[_cycles.fall.min:_cycles.fall.max] _from || !_to, _clk, ${"\\"}
            disable_sva)

  `define RISE_ASSERTS(_name, _from, _to, _cycles, _clk) ${"\\"}
    `ASSERT(_name``AboveRise_A, ${"\\"}
            $rose(_from) ##1 _from [* _cycles.rise.min] |=> ##[0:_cycles.rise.max-_cycles.rise.min] (!_from || _to), _clk, ${"\\"}
            disable_sva)

  `define CASCADED_ASSERTS(_name, _from, _to, _cycles, _clk) ${"\\"}
      `FALL_ASSERT(_name, _from, _to, _cycles, _clk) ${"\\"}
      `RISE_ASSERTS(_name, _from, _to, _cycles, _clk)

  // rst_por_aon_n is the secondary partition's own, for every power domain, as the single
  // power-domain reset manager generated it.

  // A fall in por_n_i leads to a fall in rst_por_aon_n[0].
  `FALL_ASSERT(CascadePorToAon, por_n_i[rstmgr_pkg::DomainAonSel],
               rst_por_aon_n[rstmgr_pkg::DomainAonSel], PorCycles, clk_aon_i)

  // A number of consecutive cycles with por_n_i inactive (high) should cause the aon resets to
  // become inactive. This checks POR stretching.

  // The antecedent: por_n_i rising and being active for enough cycles.

  logic scanmode;
  always_comb scanmode = prim_mubi_pkg::mubi4_test_true_strict(scanmode_i);

  logic scan_reset_n;
  always_comb scan_reset_n = !scanmode || scan_rst_ni;

  // In scanmode only scan_rst_ni controls reset, so por_n_i is ignored.
  logic aon_por_n_i;
  always_comb aon_por_n_i = por_n_i[rstmgr_pkg::DomainAonSel] && !scanmode;

  sequence PorStable_S;
    $rose(
        aon_por_n_i
    ) ##1 aon_por_n_i [* PorCycles.rise.min];
  endsequence

  // The reset stretching assertion.
  `ASSERT(StablePorToAonRise_A,
          PorStable_S |-> ##[0:(PorCycles.rise.max-PorCycles.rise.min)]
          !aon_por_n_i || rst_por_aon_n[rstmgr_pkg::DomainAonSel],
          clk_aon_i, disable_sva)

  // The scan reset to Por.
  `ASSERT(ScanRstToAonRise_A,
          scan_reset_n && scanmode |-> rst_por_aon_n[rstmgr_pkg::DomainAonSel],
          clk_aon_i, disable_sva)

  logic [rstmgr_pkg::PowerDomains-1:0] effective_aon_rst_n;
  always_comb
    effective_aon_rst_n = rst_por_aon_n & {rstmgr_pkg::PowerDomains{scan_reset_n}};

  // The internal reset is triggered by one of synchronized por.
  logic [rstmgr_pkg::PowerDomains-1:0] por_rst_n;
  always_comb por_rst_n = rst_por_aon_n;

  logic [rstmgr_pkg::PowerDomains-1:0] local_rst_or_lc_req_n;
  always_comb local_rst_or_lc_req_n = por_rst_n & ~pwr_i.rst_lc_req;

  logic [rstmgr_pkg::PowerDomains-1:0] lc_rst_or_sys_req_n;
  always_comb lc_rst_or_sys_req_n = por_rst_n & ~pwr_i.rst_sys_req;

  for (genvar pd = 0; pd < rstmgr_pkg::PowerDomains; ++pd) begin : g_power_domains
    // The root lc reset is triggered either by the internal reset, or by the pwr_i.rst_lc_req
    // input. The latter is checked independently in pwrmgr_rstmgr_sva_if.
    `CASCADED_ASSERTS(CascadeLocalRstToLc, local_rst_or_lc_req_n[pd], pwr_o.rst_lc_src_n[pd],
                      LcCycles, clk_i)

    // The root sys reset is triggered by the lc reset, or independently by external requests.
    // The latter is checked independently in pwrmgr_rstmgr_sva_if.
    `CASCADED_ASSERTS(CascadeLcToSys, lc_rst_or_sys_req_n[pd], pwr_o.rst_sys_src_n[pd], SysCycles,
                      clk_i)
  end

  // The leaf resets that this partition generates follow their parents. The parents are the lc and
  // sys roots, and the effective aon reset for the por resets.
% for name, rst, shadowed, domain, bounds in links:
<%
parent = rsts[rst]['parent']
above = {'lc_src': f"pwr_o.rst_lc_src_n[rstmgr_pkg::Domain{domain}Sel]",
         'sys_src': f"pwr_o.rst_sys_src_n[rstmgr_pkg::Domain{domain}Sel]",
         'por_aon': f"effective_aon_rst_n[rstmgr_pkg::Domain{domain}Sel]"}[parent]
below = rst_x(rsts[rst], rst + ('_shadowed' if shadowed else ''), domain)
%>\
  `CASCADED_ASSERTS(${name}, ${above},
                    ${below},
                    ${bounds}, clk_${rsts[rst]['clock']}_i)
% endfor

  `undef FALL_ASSERT
  `undef RISE_ASSERTS
  `undef CASCADED_ASSERTS
endinterface
