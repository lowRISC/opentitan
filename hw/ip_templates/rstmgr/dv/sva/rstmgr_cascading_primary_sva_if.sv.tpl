// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The cascading checks of the single power-domain reset manager, for the resets that the primary
// partition generates. rstmgr_bind binds this interface to rstmgr_part_primary.
// rstmgr_cascading_secondary_sva_if has the checks of the resets that the secondary partition
// generates.
<%
from topgen.lib import Name
from ipgen.manager_split import (rstmgr_clocks, rstmgr_hosted_domains, rstmgr_is_array,
                                 rstmgr_out_domains, rstmgr_routed_roots)
part = 'primary'
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
OUT = 'resets_o'

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
interface rstmgr_cascading_primary_sva_if (
% for clk in part_clks:
  input logic clk_${clk}_i,
% endfor
  input logic scan_rst_ni,
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input rstmgr_pkg::intraip_s2p_t intraip_s2p_i,
  input rstmgr_pkg::rstmgr_out_primary_t resets_o
);
<%
# The secondary partition generates the roots. The ones that the leaves here need cross in
# intraip_s2p, as rst_<root>_n_<power domain>.
routed_roots = set(rstmgr_routed_roots(leaf_rsts))
for name, rst, shadowed, domain, bounds in links:
  assert (rsts[rst]['parent'], domain) in routed_roots, (
      f"{name}: the root {rsts[rst]['parent']} of {rst} in {domain} does not cross to the "
      "primary partition")
%>\
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

  logic scanmode;
  always_comb scanmode = prim_mubi_pkg::mubi4_test_true_strict(scanmode_i);

  logic scan_reset_n;
  always_comb scan_reset_n = !scanmode || scan_rst_ni;

  // The leaf resets that this partition generates follow their parents, which cross from the
  // secondary partition. The parents are the lc and sys roots, and the aon reset for the por
  // resets.
% for name, rst, shadowed, domain, bounds in links:
<%
parent = rsts[rst]['parent']
root = f"intraip_s2p_i.rst_{parent}_n_{domain.lower()}"
above = f"({root} && scan_reset_n)" if parent == 'por_aon' else root
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
