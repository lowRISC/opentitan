# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code to load a top complete configuration from a Hjson file'''

import hjson

from collections import OrderedDict
from collections.abc import KeysView
from pathlib import Path
from typing import Dict

from reggen.inter_signal import InterSignal
from reggen.params import BaseParam, Parameter, LocalParam, RandParameter
from reggen.interrupt import IntrType

from .merge import _get_clock_group_name
from .clocks import Clocks, GroupProxy, UnmanagedClocks
from .resets import Resets
from .validate import Flash


def _check_equivalent(actual: object, loaded: object, path: str) -> (bool, str):
    # The loaded object can be an OrderedDict when the actual is just a dict.
    type_ok = (isinstance(actual, dict) and isinstance(loaded, OrderedDict)) or \
        (isinstance(actual, KeysView) and isinstance(loaded, KeysView))
    assert type(actual) == type(loaded) or type_ok, f"objects at {path} do not have " + \
        "the same type: {} vs {}".format(type(actual), type(loaded))  # noqa: E721

    if isinstance(actual, list):
        assert len(actual) == len(loaded), f"lists at {path} do not have the same length: " + \
            "{} vs {}".format(len(actual), len(loaded))
        for i in range(len(actual)):
            _check_equivalent(actual[i], loaded[i], f"{path}[{i}]")

    elif isinstance(actual, dict) or isinstance(actual, OrderedDict):
        _check_equivalent(actual.keys(), loaded.keys(), f"{path}.keys()")
        for x in actual.keys():
            _check_equivalent(actual[x], loaded[x], f"{path}.{x}")

    elif getattr(actual, "__dict__", None):
        _check_equivalent(actual.__dict__, loaded.__dict__, path)

    else:
        assert actual == loaded, f"objects at {path} are not equal: " + \
            "{} vs {}".format(actual, loaded)


_CLASSES = {
    'InterSignal': InterSignal,
    'BaseParam': BaseParam,
    'Parameter': Parameter,
    'LocalParam': LocalParam,
    'RandParameter': RandParameter,
    'Flash': Flash,
}


def _topcfg_hook(obj):
    """
    The main purpose of this hook is to handle classes that were serialized
    with a 'class' attribute. Those will be deserialize at this point.
    """
    obj = OrderedDict(obj)
    if 'class' in obj and obj['class'] in _CLASSES:
        return _CLASSES[obj['class']].fromdict(obj)
    return obj


class CompleteTopCfg:
    """
    An object representing a complete top configuration. This is
    the configuration produced by topgen.py and exported to Hjson.
    """

    @staticmethod
    def from_path(path: Path) -> object:
        """
        Load a configuration from the Hjson produced by topgen.
        """
        return CompleteTopCfg.from_hjson(
            hjson.loads(
                path.read_text(),
                object_pairs_hook=_topcfg_hook,
                use_decimal=True
            )
        )

    @staticmethod
    def from_hjson(topcfg: Dict[str, object]) -> object:
        """
        Load a configuration from an already parsed Hjson.
        """

        topcfg["clocks"] = Clocks.fromdict(topcfg["clocks"])
        topcfg['unmanaged_clocks'] = UnmanagedClocks(topcfg['unmanaged_clocks'])
        topcfg['resets'] = Resets.fromdict(topcfg['resets'], topcfg["clocks"])
        # The modules need some fixing.
        for mod in topcfg['module']:
            base_addrs = mod['base_addrs']
            if 'null' in base_addrs:
                base_addrs[None] = base_addrs['null']
                del base_addrs['null']
        # The interrupts as well.
        for intr in topcfg['interrupt']:
            if intr["intr_type"] == "IntrType.Status":
                intr["intr_type"] = IntrType.Status
            elif intr["intr_type"] == "IntrType.Event":
                intr["intr_type"] = IntrType.Event
            else:
                assert False, "unknown interrupt type {}".format(intr["intr_type"])
        # Alert handlers.
        for alert in topcfg['alert_lpgs']:
            alert['clock_group'] = GroupProxy.fromdict(alert['clock_group'], topcfg['clocks'])
        # The clocks need some fixing. This reimplements part of extract_clocks.
        for ep in topcfg['module'] + topcfg['memory'] + topcfg['xbar']:
            for port, clk in ep['clock_srcs'].items():
                group_name, src_name = _get_clock_group_name(clk, ep['clock_group'])
                group = topcfg["clocks"].groups[group_name]
                if group.src == 'ext':
                    name = "{}_i".format(src_name)
                elif group.unique:
                    name = "{}_{}".format(src_name, ep["name"])
                else:
                    name = "{}_{}".format(src_name, group_name)
                clk_name = "clk_" + name
                group.clocks[clk_name].add_endpoint(ep["name"], port)

        return topcfg

    @staticmethod
    def check_equivalent(actual: Dict[str, object], loaded: Dict[str, object]):
        """
        Check if the two configurations are equivalent, ie they have exactly
        the same types and same content. Throws an exception in case of error.
        """
        try:
            return _check_equivalent(actual, loaded, "")
        except AssertionError as exc:
            raise RuntimeError(
                "Serialized Hjson file is not equivalent to the in-memory one.\n" +
                "You can find the problematic section by running:\n" +
                "cat /path/to/file | hjson -c | jq <the path of the error>"
            ) from exc
