# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from copy import deepcopy
from pathlib import Path
import hjson

import re


def is_ipcfg(ip: Path) -> bool:  # return bool
    log.info("IP Path: %s" % repr(ip))
    ip_name = ip.parents[1].name
    hjson_name = ip.name

    log.info("IP Name(%s) and HJSON name (%s)" % (ip_name, hjson_name))

    if ip_name + ".hjson" == hjson_name or ip_name + "_reg.hjson" == hjson_name:
        return True
    return False


def search_ips(ip_path):  # return list of config files
    # list the every hjson file
    p = ip_path.glob('*/data/*.hjson')

    # filter only ip_name/data/ip_name{_reg|''}.hjson
    ips = [x for x in p if is_ipcfg(x)]

    log.info("Filtered-in IP files: %s" % repr(ips))
    return ips


def is_xbarcfg(xbar_obj):
    if "type" in xbar_obj and xbar_obj["type"] == "xbar":
        return True

    return False


def get_hjsonobj_xbars(xbar_path):
    """ Search crossbars hjson files from given path.

    Search every hjson in the directory and check hjson type.
    It could be type: "top" or type: "xbar"
    returns [(name, obj), ... ]
    """
    p = xbar_path.glob('*.hjson')
    try:
        xbar_objs = [hjson.load(x.open('r'), use_decimal=True) for x in p]
    except ValueError:
        raise Systemexit(sys.exc_info()[1])

    xbar_objs = [x for x in xbar_objs if is_xbarcfg(x)]

    return xbar_objs


def get_module_by_name(top, name):
    """Search in top["module"] by name
    """
    module = None
    for m in top["module"]:
        if m["name"] == name:
            module = m
            break

    return module


def get_signal_by_name(module, name):
    """Return the signal struct with the type input/output/inout
    """
    result = None
    for s in module["available_input_list"] + module[
            "available_output_list"] + module["available_inout_list"]:
        if s["name"] == name:
            result = s
            break

    return result


def add_prefix_to_signal(signal, prefix):
    """Add prefix to module signal format { name: "sig_name", width: NN }
    """
    result = deepcopy(signal)

    if not "name" in signal:
        raise SystemExit("signal {} doesn't have name field".format(signal))

    result["name"] = prefix + "_" + signal["name"]

    return result


def get_ms_name(name):
    """Split module_name.signal_name to module_name , signal_name
    """

    tokens = name.split('.')

    if len(tokens) == 0:
        raise SystemExit("This to be catched in validate.py")

    module = tokens[0]
    signal = None
    if len(tokens) == 2:
        signal = tokens[1]

    return module, signal


def parse_pad_field(padstr):
    """Parse PadName[NN...NN] or PadName[NN] or just PadName
    """
    match = re.match(r'^([A-Za-z0-9_]+)(\[([0-9]+)(\.\.([0-9]+))?\]|)', padstr)
    return match.group(1), match.group(3), match.group(5)


def get_pad_list(padstr):
    pads = []

    pad, first, last = parse_pad_field(padstr)
    if first is None:
        first = 0
        last = 0
    elif last is None:
        last = first
    first = int(first, 0)
    last = int(last, 0)
    width = first - last + 1

    for p in range(first, last + 1):
        pads.append({"name": pad, "index": p})

    return pads
