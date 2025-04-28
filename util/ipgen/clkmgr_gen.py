# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Provides support functions for clkmgr ipgen."""

import math
from collections import OrderedDict
from typing import List

from basegen.typing import ConfigT, ParamsT
from topgen.clocks import Clocks, ClockSignal
from topgen.lib import find_module

def get_clkmgr_params(top: ConfigT) -> ParamsT:
    """Gets parameters for clkmgr ipgen from top config."""
    clocks = top["clocks"]
    assert isinstance(clocks, Clocks)

    typed_clocks = clocks.typed_clocks()
    hint_names = typed_clocks.hint_names()

    typed_clks = OrderedDict({
        ty: {
            nm: {
                "src_name": sig.src.name,
                "endpoint_ip": sig.endpoints[0][0]
            }
            for nm, sig in mp.items() if isinstance(sig, ClockSignal)
        }
        for ty, mp in typed_clocks._asdict().items() if isinstance(mp, dict)
    })

    # Will connect to alert_handler
    with_alert_handler = find_module(top['module'],
                                         'alert_handler') is not None

    return {
        "src_clks":
        OrderedDict({name: vars(obj)
                     for name, obj in clocks.srcs.items()}),
        "derived_clks":
        OrderedDict(
            {name: vars(obj)
             for name, obj in clocks.derived_srcs.items()}),
        "typed_clocks":
        OrderedDict({ty: d
                     for ty, d in typed_clks.items() if d}),
        "hint_names":
        hint_names,
        "parent_child_clks":
        typed_clocks.parent_child_clks,
        "exported_clks":
        top["exported_clks"],
        "number_of_clock_groups":
        len(clocks.groups),
        "with_alert_handler":
        with_alert_handler,
    }


def get_all_srcs(src_clks: ConfigT, derived_clks: ConfigT) -> ConfigT:
    """Returns a dict of all source and derived clocks.

    The items in the dictionary are a dictionary containing the
    SourceClock or DerivedSourceClock attributes for the  corresponding
    clock.
    """
    all_srcs = src_clks.copy()
    all_srcs.update(derived_clks)
    return all_srcs


def get_rg_srcs(typed_clocks: ConfigT) -> List[str]:
    return list(sorted({sig['src_name'] for sig
                       in typed_clocks['rg_clks'].values()}))


def get_hint_targets(typed_clocks: ConfigT) -> List[str]:
    return [sig['endpoint_ip'] for sig in typed_clocks['hint_clks'].values()]
