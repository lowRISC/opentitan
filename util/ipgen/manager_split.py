# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Support functions for the templates of the split clock and reset managers.

Each manager is split into a primary partition and a secondary partition. The configuration of the
top says what each partition hosts, and topgen puts this into the ipconfig:

 - clkmgr: the partition that has a source clock in its clock_srcs receives it
   (src_clks[...]['clkmgr_partition']). That partition hosts the clocks of the source.
 - rstmgr: the partition in a reset's power domain generates the reset, with the clock that it
   receives or gets from the other partition (output_rsts[...]['partition'], by power domain). The
   secondary partition hosts the roots of the reset tree.

The functions here apply that data. They also define the layout of the output structs, so that the
templates and topgen agree on it.

The two managers handle clocks and resets in the same way:

 - A signal enters a manager once, in the partition of the power domain that generates it. A
   partition that needs it and does not receive it gets it from the other partition.
 - A partition outputs what its power domain uses.
 - What the other domain needs crosses once, in intraip_s2p or intraip_p2s.
 - The primary partition outputs all the clock gating and reset asserted indications, for the
   alert handlers.

The remaining differences have these causes:

 - Resets have power-domain variants. A reset is generated, routed and output per reset and power
   domain. Its field is an array over the power domains or a single bit (rstmgr_is_array), and a
   shadowed reset has a twin. A clock is a single signal.
 - Clocks share nets. All the root-gated clocks of a source are its root clock, and the feed-through
   clocks are buffers of the source. So the clkmgr routes nets (clkmgr_routed_nets), while the
   rstmgr routes single bits.
 - The templates differ in structure. The primary partition of the clkmgr makes the derived clocks
   (the dividers). The secondary partition of the rstmgr hosts the roots of the reset tree (the POR
   handling). So the secondary partition of the rstmgr always uses the always-on clock, which is
   also the only clock that it receives: every other clock enters the primary partition
   (rstmgr_clocks). The clock ports of the clkmgr are its source clocks.
 - topgen already resolved clock connections during merge and reset connections later, in the
   templates. So merge records the consumers of a clock (ClockSignal.add_endpoint), while
   lib._rstmgr_consumers collects the consumers of a reset from the modules afterwards. topgen
   builds the clock paths from the source (lib.get_clock_prefixes) and the reset paths from the
   partition (lib.get_reset_prefixes).
 - topgen already built the clkmgr parameters in ipgen/clkmgr_gen.py and the rstmgr parameters in
   topgen.py. So the partition data enters each ipconfig there.
"""

from typing import Dict, List, NamedTuple, Optional, Sequence, Tuple

from reggen.lib import PART_PRIMARY, PART_SECONDARY
from topgen.lib import AON_CLOCK, rstmgr_clock_entry_partitions
from topgen.lib import rstmgr_is_array  # noqa: F401 (the templates import it from here)


def clkmgr_split_srcs(src_clks: Dict) -> Tuple[List, List]:
    """Return the clkmgr source clocks as (primary, secondary), by the partition that receives each
    one.

    Raise a ValueError if a source clock has no partition.
    """
    for name, src in src_clks.items():
        if src.get('clkmgr_partition') not in (PART_PRIMARY, PART_SECONDARY):
            raise ValueError(f"the source clock {name} is not assigned to a partition of the "
                             "clkmgr (clkmgr_partition). This clkmgr is split into two "
                             "partitions: the top must define domain_secondary for it and the "
                             "clock_srcs of both partitions")
    secondary = [s for s in src_clks.values() if s['clkmgr_partition'] == PART_SECONDARY]
    primary = [s for s in src_clks.values() if s['clkmgr_partition'] == PART_PRIMARY]
    return primary, secondary


def clkmgr_secondary_ft_clks(typed_clocks: Dict, src_clks: Dict) -> Dict:
    """Return, by name, the feed-through clocks of the sources that the secondary partition
    receives.

    These are the only clocks that the secondary partition generates. It hosts one buffer for each
    of them. The primary partition generates all the other clocks.
    """
    _, secondary = clkmgr_split_srcs(src_clks)
    names = {s['name'] for s in secondary}
    return {k: v for k, v in typed_clocks['ft_clks'].items() if v['src_name'] in names}


def _all_clks(typed_clocks: Dict) -> Dict:
    """Return all the clocks of the clkmgr by name, in the order that the templates use
    (feed-through, hint, root-gated and software-gated clocks).
    """
    clks = {}
    for kind in ('ft_clks', 'hint_clks', 'rg_clks', 'sw_clks'):
        clks.update(typed_clocks.get(kind, {}))
    return clks


def clkmgr_generated_clks(typed_clocks: Dict, src_clks: Dict, partition: str) -> List[str]:
    """Return the clocks that a partition generates.

    The secondary partition generates the feed-through clocks of its sources. The primary partition
    generates all the other clocks, as it gates them.
    """
    secondary = clkmgr_secondary_ft_clks(typed_clocks, src_clks)
    return [k for k in _all_clks(typed_clocks) if (k in secondary) == (partition == PART_SECONDARY)]


def clkmgr_out_clks(typed_clocks: Dict, partition: str) -> List[str]:
    """Return the clocks that a partition outputs, which are the clocks that its power domain uses
    (out_partitions).

    Raise a ValueError if topgen did not provide out_partitions for a clock.
    """
    out = []
    for name, clk in _all_clks(typed_clocks).items():
        if 'out_partitions' not in clk:
            raise ValueError(f"the clock {name} has no out_partitions, topgen must provide it")
        if partition in clk['out_partitions']:
            out.append(name)
    return out


def clkmgr_routed_clks(typed_clocks: Dict, src_clks: Dict, to_partition: str) -> List[str]:
    """Return the clocks that the other partition generates and `to_partition` outputs.

    Each of these clocks crosses the partition boundary once, inside the clkmgr.
    """
    other = PART_PRIMARY if to_partition == PART_SECONDARY else PART_SECONDARY
    generated_by_other = set(clkmgr_generated_clks(typed_clocks, src_clks, other))
    return [k for k in clkmgr_out_clks(typed_clocks, to_partition) if k in generated_by_other]


def clkmgr_routed_nets(typed_clocks: Dict, src_clks: Dict, to_partition: str) -> Dict:
    """Return, by name, the nets that carry the clocks routed to `to_partition`, each net once.

    Several clocks are often the same net. All the root-gated clocks of a source are its root clock
    clk_<src>_root, and the feed-through clocks of a source are buffers of clk_<src>. Each entry is
    {'kind': 'ft' | 'root' | 'clk', 'clocks': [...]}. The partition buffers a feed-through clock
    again from the net. A root-gated or individually gated clock is the net itself.
    """
    nets = {}
    for k in clkmgr_routed_clks(typed_clocks, src_clks, to_partition):
        if k in typed_clocks.get('ft_clks', {}):
            net, kind = f"clk_{typed_clocks['ft_clks'][k]['src_name']}", 'ft'
        elif k in typed_clocks.get('rg_clks', {}):
            net, kind = f"clk_{typed_clocks['rg_clks'][k]['src_name']}_root", 'root'
        else:
            net, kind = k, 'clk'
        nets.setdefault(net, {'kind': kind, 'clocks': []})['clocks'].append(k)
    return nets


class RstmgrClocks(NamedTuple):
    """The clocks of the reset manager, by partition."""
    own: str              # The clock that the reset manager itself runs on.
    aon: List[str]        # The always-on clocks.
    secondary: List[str]  # The clocks that the secondary partition uses.
    primary: List[str]    # The clocks that the primary partition uses.
    ports: Dict[str, List[str]]      # By partition, the clocks that it receives (a port each).
    forwarded: Dict[str, List[str]]  # By partition, the clocks that it gets from the other one.


def rstmgr_clocks(clk_freqs: Dict, leaf_rsts: Sequence[Dict], rst_ni: str) -> RstmgrClocks:
    """Return the clocks of each partition of the reset manager.

    A partition uses the clocks of the leaf resets that it generates, and its own clock. Its own
    clock is the clock of the leaf reset that is the reset manager's own reset (rst_ni). The
    secondary partition also uses the always-on clock, for the roots of the reset tree that it
    hosts.

    Each clock but the always-on one enters the primary partition only, which has a port for it;
    the secondary partition gets it from there, in intraip_p2s. Each partition that uses the
    always-on clock receives the one of its own power domain (rstmgr_clock_entry_partitions).
    """
    own = next(r['clock'] for r in leaf_rsts if r['name'] == rst_ni)
    aon = [c for c in clk_freqs if c == AON_CLOCK]
    used = {p: {r['clock'] for r in leaf_rsts if rstmgr_hosted_domains(r, p)} | {own}
            for p in (PART_PRIMARY, PART_SECONDARY)}
    used[PART_SECONDARY] |= set(aon)
    secondary = [c for c in clk_freqs if c in used[PART_SECONDARY]]
    primary = [c for c in clk_freqs if c in used[PART_PRIMARY]]
    users = {c: {p for p in (PART_PRIMARY, PART_SECONDARY) if c in used[p]} for c in clk_freqs}
    ports = {p: [c for c in clk_freqs
                 if users[c] and p in rstmgr_clock_entry_partitions(c, users[c])]
             for p in (PART_PRIMARY, PART_SECONDARY)}
    forwarded = {p: [c for c in clk_freqs if c in used[p] and c not in ports[p]]
                 for p in (PART_PRIMARY, PART_SECONDARY)}
    return RstmgrClocks(own, aon, secondary, primary, ports, forwarded)


def rstmgr_hosted_domains(rst: Dict, partition: str) -> List[str]:
    """Return the power domains of the output reset `rst` that `partition` drives.

    The configuration declares the partition of a reset per power domain (rst['partition']). The
    primary partition drives a reset that has no declared partition.
    """
    declared = rst.get('partition', {})
    return [d for d in rst['domains'] if declared.get(d, PART_PRIMARY) == partition]


def rstmgr_routed_roots(leaf_rsts: Sequence[Dict]) -> List[Tuple[str, str]]:
    """The reset roots that cross to the primary partition, as (root, power domain) pairs.

    The roots are hosted in the secondary partition. Unlike the resets of rstmgr_routed_rsts, which
    cross for their consumers outside the reset manager, a root crosses for the leaf resets that the
    primary partition hosts: each (parent, power domain) of those leaves crosses once.
    """
    pairs = []
    for rst in leaf_rsts:
        for domain in rstmgr_hosted_domains(rst, PART_PRIMARY):
            if (rst['parent'], domain) not in pairs:
                pairs.append((rst['parent'], domain))
    return pairs


def rstmgr_out_domains(rst: Dict, partition: str, name: Optional[str] = None) -> List[str]:
    """Return the power domains of the output reset `rst` that `partition` outputs.

    A partition outputs the variant of a reset for a power domain when the consumers of that variant
    are in the partition's power domain. topgen provides this as out_partitions. For the shadowed
    copy (`name` ends in _shadowed), topgen provides out_partitions_shadowed, so that the copy does
    not cross to a partition where no module uses it. Raise a ValueError if they are missing.
    """
    shadowed = name is not None and name.endswith('_shadowed')
    outs = rst.get('out_partitions_shadowed' if shadowed else 'out_partitions')
    if outs is None:
        raise ValueError(f"the reset {rst['name']} has no out_partitions, topgen must provide it")
    return [d for d in rst['domains'] if partition in outs.get(d, [])]


def rstmgr_routed_rsts(output_rsts: Sequence[Dict], to_partition: str) -> List[str]:
    """Return the resets that the other partition generates and `to_partition` outputs.

    They cross as the single-bit fields of the intra-IP struct (rst_<name>_n_<domain>). A reset, or
    the shadowed copy of a reset, crosses to the other partition only if a module in that
    partition's power domain uses it (out_partitions, out_partitions_shadowed).
    """
    other = PART_PRIMARY if to_partition == PART_SECONDARY else PART_SECONDARY
    out = []
    for rst in output_rsts:
        names = [rst['name']] + ([rst['name'] + '_shadowed'] if rst['shadowed'] else [])
        for n in names:
            for d in rstmgr_out_domains(rst, to_partition, n):
                if d in rstmgr_hosted_domains(rst, other):
                    out.append(f"rst_{n}_n_{d.lower()}")
    return out


def rstmgr_rst_en_routed(output_rsts: Sequence[Dict]) -> List[Tuple[str, str, str]]:
    """Return the reset asserted indications that the secondary partition generates, as (intra-IP
    field, name, power domain).

    They cross to the primary partition, which outputs all the indications, for the alert handlers.
    """
    out = []
    for rst in output_rsts:
        names = [rst['name']] + ([rst['name'] + '_shadowed'] if rst['shadowed'] else [])
        for d in rstmgr_hosted_domains(rst, PART_SECONDARY):
            out += [(f"rst_en_{n}_{d.lower()}", n, d) for n in names]
    return out
