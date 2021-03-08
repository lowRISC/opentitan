# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import re
import sys
from collections import OrderedDict
from copy import deepcopy
from pathlib import Path
from typing import Dict, Optional, Tuple

import hjson

from reggen.ip_block import IpBlock

# Ignore flake8 warning as the function is used in the template
# disable isort formating, as conflicting with flake8
from .intermodule import find_otherside_modules  # noqa : F401 # isort:skip
from .intermodule import im_portname, im_defname, im_netname  # noqa : F401 # isort:skip
from .intermodule import get_dangling_im_def # noqa : F401 # isort:skip


def is_ipcfg(ip: Path) -> bool:  # return bool
    log.info("IP Path: %s" % repr(ip))
    ip_name = ip.parents[1].name
    hjson_name = ip.name

    log.info("IP Name(%s) and HJSON name (%s)" % (ip_name, hjson_name))

    if ip_name + ".hjson" == hjson_name or ip_name + "_reg.hjson" == hjson_name:
        return True
    return False


def search_ips(ip_path):  # return list of config files
    # list the every Hjson file
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
    """ Search crossbars Hjson files from given path.

    Search every Hjson in the directory and check Hjson type.
    It could be type: "top" or type: "xbar"
    returns [(name, obj), ... ]
    """
    p = xbar_path.glob('*.hjson')
    try:
        xbar_objs = [
            hjson.load(x.open('r'),
                       use_decimal=True,
                       object_pairs_hook=OrderedDict) for x in p
        ]
    except ValueError:
        raise SystemExit(sys.exc_info()[1])

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


def intersignal_to_signalname(top, m_name, s_name) -> str:

    # TODO: Find the signal in the `inter_module_list` and get the correct signal name

    return "{m_name}_{s_name}".format(m_name=m_name, s_name=s_name)


def get_package_name_by_intermodule_signal(top, struct) -> str:
    """Search inter-module signal package with the struct name

    For instance, if `flash_ctrl` has inter-module signal package,
    this function returns the package name
    """
    instances = top["module"] + top["memory"]

    intermodule_instances = [
        x["inter_signal_list"] for x in instances if "inter_signal_list" in x
    ]

    for m in intermodule_instances:
        if m["name"] == struct and "package" in m:
            return m["package"]
    return ""


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


def add_module_prefix_to_signal(signal, module):
    """Add module prefix to module signal format { name: "sig_name", width: NN }
    """
    result = deepcopy(signal)

    if "name" not in signal:
        raise SystemExit("signal {} doesn't have name field".format(signal))

    result["name"] = module + "_" + signal["name"]
    result["module_name"] = module

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
    # width = first - last + 1

    for p in range(first, last + 1):
        pads.append(OrderedDict([("name", pad), ("index", p)]))

    return pads


# Template functions
def ljust(x, width):
    return "{:<{width}}".format(x, width=width)


def bitarray(d, width):
    """Print Systemverilog bit array

    @param d the bit width of the signal
    @param width max character width of the signal group

    For instance, if width is 4, the max d value in the signal group could be
    9999. If d is 2, then this function pads 3 spaces at the end of the bit
    slice.

    "[1:0]   " <- d:=2, width=4
    "[9999:0]" <- max d-1 value

    If d is 1, it means array slice isn't necessary. So it returns empty spaces
    """

    if d <= 0:
        log.error("lib.bitarray: Given value {} is smaller than 1".format(d))
        raise ValueError
    if d == 1:
        return " " * (width + 4)  # [x:0] needs 4 more space than char_width

    out = "[{}:0]".format(d - 1)
    return out + (" " * (width - len(str(d))))


def parameterize(text):
    """Return the value wrapping with quote if not integer nor bits
    """
    if re.match(r'(\d+\'[hdb]\s*[0-9a-f_A-F]+|[0-9]+)', text) is None:
        return "\"{}\"".format(text)

    return text


def index(i: int) -> str:
    """Return index if it is not -1
    """
    return "[{}]".format(i) if i != -1 else ""


def get_clk_name(clk):
    """Return the appropriate clk name
    """
    if clk == 'main':
        return 'clk_i'
    else:
        return "clk_{}_i".format(clk)


def get_reset_path(reset, domain, reset_cfg):
    """Return the appropriate reset path given name
    """
    # find matching node for reset
    node_match = [node for node in reset_cfg['nodes'] if node['name'] == reset]
    assert len(node_match) == 1
    reset_type = node_match[0]['type']

    # find matching path
    hier_path = ""
    if reset_type == "int":
        log.debug("{} used as internal reset".format(reset["name"]))
    else:
        hier_path = reset_cfg['hier_paths'][reset_type]

    # find domain selection
    domain_sel = ''
    if reset_type not in ["ext", "int"]:
        domain_sel = "[rstmgr_pkg::Domain{}Sel]".format(domain)

    reset_path = ""
    if reset_type == "ext":
        reset_path = reset
    else:
        reset_path = "{}rst_{}_n{}".format(hier_path, reset, domain_sel)

    return reset_path


def get_unused_resets(top):
    """Return dict of unused resets and associated domain
    """
    unused_resets = OrderedDict()
    unused_resets = {
        reset['name']: domain
        for reset in top['resets']['nodes']
        for domain in top['power']['domains']
        if reset['type'] == 'top' and domain not in reset['domains']
    }

    log.debug("Unused resets are {}".format(unused_resets))
    return unused_resets


def is_templated(module):
    """Returns an indication where a particular module is templated
    """
    if "attr" not in module:
        return False
    elif module["attr"] in ["templated"]:
        return True
    else:
        return False


def is_top_reggen(module):
    """Returns an indication where a particular module is NOT templated
       and requires top level specific reggen
    """
    if "attr" not in module:
        return False
    elif module["attr"] in ["reggen_top", "reggen_only"]:
        return True
    else:
        return False


def is_inst(module):
    """Returns an indication where a particular module should be instantiated
       in the top level
    """
    top_level_module = False
    top_level_mem = False

    if "attr" not in module:
        top_level_module = True
    elif module["attr"] in ["normal", "templated", "reggen_top"]:
        top_level_module = True
    elif module["attr"] in ["reggen_only"]:
        top_level_module = False
    else:
        raise ValueError('Attribute {} in {} is not valid'
                         .format(module['attr'], module['name']))

    if module['type'] in ['rom', 'ram_1p_scr', 'eflash']:
        top_level_mem = True

    return top_level_mem or top_level_module


def get_base_and_size(name_to_block: Dict[str, IpBlock],
                      inst: Dict[str, object],
                      ifname: Optional[str]) -> Tuple[int, int]:
    min_device_spacing = 0x1000

    block = name_to_block.get(inst['type'])
    if block is None:
        # If inst isn't the instantiation of a block, it came from some memory.
        # Memories have their sizes defined, so we can just look it up there.
        bytes_used = int(inst['size'], 0)

        # Memories don't have multiple or named interfaces, so this will only
        # work if ifname is None.
        assert ifname is None
        base_addr = inst['base_addr']

    else:
        # If inst is the instantiation of some block, find the register block
        # that corresponds to ifname
        rb = block.reg_blocks.get(ifname)
        if rb is None:
            log.error('Cannot connect to non-existent {} device interface '
                      'on {!r} (an instance of the {!r} block)'
                      .format('default' if ifname is None else repr(ifname),
                              inst['name'], block.name))
            bytes_used = 0
        else:
            bytes_used = 1 << rb.get_addr_width()

        base_addr = inst['base_addrs'][ifname]

    # Round up to min_device_spacing if necessary
    size_byte = max(bytes_used, min_device_spacing)

    if isinstance(base_addr, str):
        base_addr = int(base_addr, 0)
    else:
        assert isinstance(base_addr, int)

    return (base_addr, size_byte)
