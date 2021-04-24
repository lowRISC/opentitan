# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import re
from collections import OrderedDict
from enum import Enum
from typing import Dict, List, Tuple

from reggen.ip_block import IpBlock
from reggen.inter_signal import InterSignal
from reggen.validate import check_int
from topgen import lib

IM_TYPES = ['uni', 'req_rsp']
IM_ACTS = ['req', 'rsp', 'rcv']
IM_VALID_TYPEACT = {'uni': ['req', 'rcv'], 'req_rsp': ['req', 'rsp']}
IM_CONN_TYPE = ['1-to-1', '1-to-N', 'broadcast']


class ImType(Enum):
    Uni = 1
    ReqRsp = 2


class ImAct(Enum):
    Req = 1
    Rsp = 2
    Rcv = 3


class ImConn(Enum):
    OneToOne = 1  # req <-> {rsp,rcv} with same width
    OneToN = 2  # req width N <-> N x {rsp,rcv}s width 1
    Broadcast = 3  # req width 1 <-> N x rcvs width 1


def intersignal_format(req: Dict) -> str:
    """Determine the signal format of the inter-module connections

    @param[req] Request struct. It has instance name, package format
                and etc.
    """

    # TODO: Handle array signal
    result = "{req}_{struct}".format(req=req["inst_name"], struct=req["name"])

    # check signal length if exceeds 100

    # 7 : space + .
    # 3 : _{i|o}(
    # 6 : _{req|rsp}),
    req_length = 7 + len(req["name"]) + 3 + len(result) + 6

    if req_length > 100:
        logmsg = "signal {0} length cannot be greater than 100"
        log.warning(logmsg.format(result))
        log.warning("Please consider shorten the instance name")
    return result


def get_suffixes(ims: OrderedDict) -> Tuple[str, str]:
    """Get suffixes of the struct.

    TL-UL struct uses `h2d`, `d2h` suffixes for req, rsp pair.
    """
    if ims["package"] == "tlul_pkg" and ims["struct"] == "tl":
        return ("_h2d", "_d2h")

    return ("_req", "_rsp")


def add_intermodule_connection(obj: OrderedDict, req_m: str, req_s: str,
                               rsp_m: str, rsp_s: str):
    """Add if doesn't exist the connection

    Add a connection into obj['inter_module']['connect'] dictionary if doesn't exist.

    Parameters:
        obj:   Top dictionary object
        req_m: Requester module name
        req_s: Requester signal name
        rsp_m: Responder module name
        rsp_s: Responder signal name

    Returns:
        No return type for this function
    """
    req_key = "{}.{}".format(req_m, req_s)
    rsp_key = "{}.{}".format(rsp_m, rsp_s)

    connect = obj["inter_module"]["connect"]
    if req_key in connect:
        # check if rsp has data
        if rsp_key in connect[req_key]:
            return
        req_key.append(rsp_key)
        return

    # req_key is not in connect:
    # check if rsp_key
    if rsp_key in connect:
        # check if rsp has data
        if req_key in connect[rsp_key]:
            return
        rsp_key.append(req_key)
        return

    # Add new key and connect
    connect[req_key] = [rsp_key]


def autoconnect_xbar(topcfg: OrderedDict,
                     name_to_block: Dict[str, IpBlock],
                     xbar: OrderedDict) -> None:
    # The crossbar is connecting to modules and memories in topcfg, plus
    # possible external connections. Make indices for the modules and memories
    # for quick lookup and add some assertions to make sure no name appears in
    # multiple places.
    name_to_module = {}
    for mod in topcfg['module']:
        assert mod['name'] not in name_to_module
        if lib.is_inst(mod):
            name_to_module[mod['name']] = mod

    name_to_memory = {}
    for mem in topcfg['memory']:
        assert mem['name'] not in name_to_memory
        if lib.is_inst(mem):
            name_to_memory[mem['name']] = mem

    # The names of modules and memories should be disjoint
    assert not (set(name_to_module.keys()) & set(name_to_memory.keys()))

    external_names = (set(topcfg['inter_module']['top']) |
                      set(topcfg["inter_module"]["external"].keys()))

    ports = [x for x in xbar["nodes"] if x["type"] in ["host", "device"]]
    for port in ports:
        # Here, we expect port_name to either be a single identifier (in which
        # case, it's taken as the name of some module or memory) to be a dotted
        # pair MOD.INAME where MOD is the name of some module and INAME is the
        # associated interface name.
        name_parts = port['name'].split('.', 1)
        port_base = name_parts[0]
        port_iname = name_parts[1] if len(name_parts) > 1 else None
        esc_name = port['name'].replace('.', '__')

        if port["xbar"]:
            if port_iname is not None:
                log.error('A crossbar connection may not '
                          'have a target of the form MOD.INAME (saw {!r})'
                          .format(port['name']))
                continue

            if port["type"] == "host":
                # Skip as device will add connection
                continue

            # Device port adds signal
            add_intermodule_connection(obj=topcfg,
                                       req_m=xbar["name"],
                                       req_s="tl_" + esc_name,
                                       rsp_m=esc_name,
                                       rsp_s="tl_" + xbar["name"])
            continue  # xbar port case

        port_mod = name_to_module.get(port_base)
        port_mem = name_to_memory.get(port_base)
        assert port_mod is None or port_mem is None

        if not (port_mod or port_mem):
            # if not in module, memory, should be existed in top or ext field
            module_key = "{}.tl_{}".format(xbar["name"], esc_name)
            if module_key not in external_names:
                log.error("Inter-module key {} cannot be found in module, "
                          "memory, top, or external lists.".format(module_key))

            continue

        if port_iname is not None and port_mem is not None:
            log.error('Cannot make connection for {!r}: the base of the name '
                      'points to a memory but memories do not support '
                      'interface names.'
                      .format(port['name']))

        is_host = port['type'] == 'host'

        # If the hit is a module, it originally came from reggen (via
        # merge.py's amend_ip() function). In this case, we should have a
        # BusInterfaces object as well as a list of InterSignal objects.
        #
        # If not, this is a memory that will just have a dictionary of inter
        # signals.
        if port_mod is not None:
            block = name_to_block[port_mod['type']]
            try:
                sig_name = block.bus_interfaces.find_port_name(is_host,
                                                               port_iname)
            except KeyError:
                log.error('Cannot make {} connection for {!r}: the base of '
                          'the target module has no matching bus interface.'
                          .format('host' if is_host else 'device',
                                  port['name']))
                continue
        else:
            inter_signal_list = port_mem['inter_signal_list']
            act = 'req' if is_host else 'rsp'
            matches = [
                x for x in inter_signal_list
                if (x.get('package') == 'tlul_pkg' and
                    x['struct'] == 'tl' and
                    x['act'] == act)
            ]
            if not matches:
                log.error('Cannot make {} connection for {!r}: the memory '
                          'has no signal with an action of {}.'
                          .format('host' if is_host else 'device',
                                  port['name'],
                                  act))
                continue

            assert len(matches) == 1
            sig_name = matches[0]['name']

        add_intermodule_connection(obj=topcfg,
                                   req_m=port_base,
                                   req_s=sig_name,
                                   rsp_m=xbar["name"],
                                   rsp_s="tl_" + esc_name)


def autoconnect(topcfg: OrderedDict, name_to_block: Dict[str, IpBlock]):
    """Matching the connection based on the naming rule
    between {memory, module} <-> Xbar.
    """

    # Add xbar connection to the modules, memories
    for xbar in topcfg["xbar"]:
        autoconnect_xbar(topcfg, name_to_block, xbar)


def _get_default_name(sig, suffix):
    """Generate default for a net if one does not already exist.
    """

    # The else case covers the scenario where neither package nor default is provided.
    # Specifically, the interface is 'logic' and has no default value.
    # In this situation, just return 0's
    if sig['default']:
        return sig['default']
    elif sig['package']:
        return "{}::{}_DEFAULT".format(sig['package'], (sig["struct"] + suffix).upper())
    else:
        return "'0"


def elab_intermodule(topcfg: OrderedDict):
    """Check the connection of inter-module and categorize them

    In the top template, it uses updated inter_module fields to create
    connections between the modules (incl. memories). This function is to
    create and check the validity of the connections `inter_module` using IPs'
    `inter_signal_list`.
    """

    list_of_intersignals = []

    if "inter_signal" not in topcfg:
        topcfg["inter_signal"] = OrderedDict()

    # Gather the inter_signal_list
    instances = topcfg["module"] + topcfg["memory"] + topcfg["xbar"] + \
        topcfg["host"] + topcfg["port"]

    for x in instances:
        old_isl = x.get('inter_signal_list')
        if old_isl is None:
            continue

        new_isl = []
        for entry in old_isl:
            # Convert any InterSignal objects to the expected dictionary format.
            sig = (entry.as_dict()
                   if isinstance(entry, InterSignal)
                   else entry.copy())

            # Add instance name to the entry and add to list_of_intersignals
            sig["inst_name"] = x["name"]
            list_of_intersignals.append(sig)
            new_isl.append(sig)

        x['inter_signal_list'] = new_isl

    # Add field to the topcfg
    topcfg["inter_signal"]["signals"] = list_of_intersignals

    # TODO: Cross check Can be done here not in validate as ipobj is not
    # available in validate
    error = check_intermodule(topcfg, "Inter-module Check")
    assert error == 0, "Inter-module validation is failed cannot move forward."

    # intermodule
    definitions = []

    # Check the originator
    # As inter-module connection allow only 1:1, 1:N, or N:1, pick the most
    # common signals. If a requester connects to multiple responders/receivers,
    # the requester is main connector so that the definition becomes array.
    #
    # For example:
    #  inter_module: {
    #    'connect': {
    #      'pwr_mgr.pwrup': ['lc.pwrup', 'otp.pwrup']
    #    }
    #  }
    # The tool adds `struct [1:0] pwr_mgr_pwrup`
    # It doesn't matter whether `pwr_mgr.pwrup` is requester or responder.
    # If the key is responder type, then the connection is made in reverse,
    # such that `lc.pwrup --> pwr_mgr.pwrup[0]` and
    # `otp.pwrup --> pwr_mgr.pwrup[1]`

    uid = 0  # Unique connection ID across the top

    for req, rsps in topcfg["inter_module"]["connect"].items():
        log.info("{req} --> {rsps}".format(req=req, rsps=rsps))

        # Split index
        req_module, req_signal, req_index = filter_index(req)

        # get the module signal
        req_struct = find_intermodule_signal(list_of_intersignals, req_module,
                                             req_signal)

        # decide signal format based on the `key`
        sig_name = intersignal_format(req_struct)
        req_struct["top_signame"] = sig_name

        # Find package in req, rsps
        if "package" in req_struct:
            package = req_struct["package"]
        else:
            for rsp in rsps:
                rsp_module, rsp_signal, rsp_index = filter_index(rsp)
                rsp_struct = find_intermodule_signal(list_of_intersignals,
                                                     rsp_module, rsp_signal)
                if "package" in rsp_struct:
                    package = rsp_struct["package"]
                    break
            if not package:
                package = ""

        # Add to definition
        if req_struct["type"] == "req_rsp":
            req_suffix, rsp_suffix = get_suffixes(req_struct)
            req_default = _get_default_name(req_struct, req_suffix)
            rsp_default = _get_default_name(req_struct, rsp_suffix)

            # based on the active direction of the req_struct, one of the directions does not
            # need a default since it will be an output
            if (req_struct["act"] == 'req'):
                req_default = ''
            else:
                rsp_default = ''

            # Add two definitions
            definitions.append(
                OrderedDict([('package', package),
                             ('struct', req_struct["struct"] + req_suffix),
                             ('signame', sig_name + "_req"),
                             ('width', req_struct["width"]),
                             ('type', req_struct["type"]),
                             ('end_idx', req_struct["end_idx"]),
                             ('act', req_struct["act"]),
                             ('suffix', "req"),
                             ('default', req_default)]))
            definitions.append(
                OrderedDict([('package', package),
                             ('struct', req_struct["struct"] + rsp_suffix),
                             ('signame', sig_name + "_rsp"),
                             ('width', req_struct["width"]),
                             ('type', req_struct["type"]),
                             ('end_idx', req_struct["end_idx"]),
                             ('act', req_struct["act"]),
                             ('suffix', "rsp"),
                             ('default', rsp_default)]))
        else:
            # unidirection
            default = _get_default_name(req_struct, "")
            definitions.append(
                OrderedDict([('package', package),
                             ('struct', req_struct["struct"]),
                             ('signame', sig_name),
                             ('width', req_struct["width"]),
                             ('type', req_struct["type"]),
                             ('end_idx', req_struct["end_idx"]),
                             ('act', req_struct["act"]),
                             ('suffix', ""),
                             ('default', default)]))

        req_struct["index"] = -1

        for i, rsp in enumerate(rsps):
            # Split index
            rsp_module, rsp_signal, rsp_index = filter_index(rsp)

            rsp_struct = find_intermodule_signal(list_of_intersignals,
                                                 rsp_module, rsp_signal)

            # determine the signal name

            rsp_struct["top_signame"] = sig_name
            if req_struct["type"] == "uni" and req_struct[
                    "top_type"] == "broadcast":
                rsp_struct["index"] = -1
            elif rsp_struct["width"] == req_struct["width"] and len(rsps) == 1:
                rsp_struct["index"] = -1
            else:
                rsp_struct["index"] = -1 if req_struct["width"] == 1 else i

            # Assume it is logic
            # req_rsp doesn't allow logic
            if req_struct["struct"] == "logic":
                assert req_struct[
                    "type"] != "req_rsp", "logic signal cannot have req_rsp type"

            # increase Unique ID
            uid += 1

    # TODO: Check unconnected port
    if "top" not in topcfg["inter_module"]:
        topcfg["inter_module"]["top"] = []

    for s in topcfg["inter_module"]["top"]:
        sig_m, sig_s, sig_i = filter_index(s)
        assert sig_i == -1, 'top net connection should not use bit index'
        sig = find_intermodule_signal(list_of_intersignals, sig_m, sig_s)
        sig_name = intersignal_format(sig)
        sig["top_signame"] = sig_name
        if "index" not in sig:
            sig["index"] = -1

        if sig["type"] == "req_rsp":
            req_suffix, rsp_suffix = get_suffixes(sig)
            # Add two definitions
            definitions.append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"] + req_suffix),
                             ('signame', sig_name + "_req"),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('end_idx', -1),
                             ('default', sig["default"])]))
            definitions.append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"] + rsp_suffix),
                             ('signame', sig_name + "_rsp"),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('end_idx', -1),
                             ('default', sig["default"])]))
        else:  # if sig["type"] == "uni":
            definitions.append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"]), ('signame', sig_name),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('end_idx', -1),
                             ('default', sig["default"])]))

    topcfg["inter_module"].setdefault('external', [])
    topcfg["inter_signal"].setdefault('external', [])

    for s, port in topcfg["inter_module"]["external"].items():
        sig_m, sig_s, sig_i = filter_index(s)
        assert sig_i == -1, 'top net connection should not use bit index'
        sig = find_intermodule_signal(list_of_intersignals, sig_m, sig_s)

        # To make netname `_o` or `_i`
        sig['external'] = True

        sig_name = port if port != "" else intersignal_format(sig)

        # if top signame already defined, then a previous connection category
        # is already connected to external pin.  Sig name is only used for
        # port definition
        conn_type = False
        if "top_signame" not in sig:
            sig["top_signame"] = sig_name
        else:
            conn_type = True

        if "index" not in sig:
            sig["index"] = -1

        # Add the port definition to top external ports
        index = sig["index"]
        netname = sig["top_signame"]
        if sig["type"] == "req_rsp":
            req_suffix, rsp_suffix = get_suffixes(sig)
            if sig["act"] == "req":
                req_sigsuffix, rsp_sigsuffix = ("_o", "_i")

            else:
                req_sigsuffix, rsp_sigsuffix = ("_i", "_o")

            topcfg["inter_signal"]["external"].append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"] + req_suffix),
                             ('signame', sig_name + "_req" + req_sigsuffix),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('default', sig["default"]),
                             ('direction',
                              'out' if sig['act'] == "req" else 'in'),
                             ('conn_type', conn_type),
                             ('index', index),
                             ('netname', netname + req_suffix)]))
            topcfg["inter_signal"]["external"].append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"] + rsp_suffix),
                             ('signame', sig_name + "_rsp" + rsp_sigsuffix),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('default', sig["default"]),
                             ('direction',
                              'in' if sig['act'] == "req" else 'out'),
                             ('conn_type', conn_type),
                             ('index', index),
                             ('netname', netname + rsp_suffix)]))
        else:  # uni
            if sig["act"] == "req":
                sigsuffix = "_o"
            else:
                sigsuffix = "_i"
            topcfg["inter_signal"]["external"].append(
                OrderedDict([('package', sig.get("package", "")),
                             ('struct', sig["struct"]),
                             ('signame', sig_name + sigsuffix),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('default', sig["default"]),
                             ('direction',
                              'out' if sig['act'] == "req" else 'in'),
                             ('conn_type', conn_type),
                             ('index', index),
                             ('netname', netname)]))

    for sig in topcfg["inter_signal"]["signals"]:
        # Check if it exist in definitions
        if "top_signame" in sig:
            continue

        # Set index to -1
        sig["index"] = -1

        # TODO: Handle the unconnected port rule

    if "definitions" not in topcfg["inter_signal"]:
        topcfg["inter_signal"]["definitions"] = definitions


def filter_index(signame: str) -> Tuple[str, str, int]:
    """If the signal has array indicator `[N]` then split and return name and
    array index. If not, array index is -1.

    param signame module.sig{[N]}

    result (module_name, signal_name, array_index)
    """
    m = re.match(r'(\w+)\.(\w+)(\[(\d+)\])*', signame)

    if not m:
        # Cannot match the pattern
        return "", "", -1

    if m.group(3):
        # array index is not None
        return m.group(1), m.group(2), m.group(4)

    return m.group(1), m.group(2), -1


def find_intermodule_signal(sig_list, m_name, s_name) -> Dict:
    """Return the intermodule signal structure
    """

    filtered = [
        x for x in sig_list if x["name"] == s_name and x["inst_name"] == m_name
    ]

    if len(filtered) == 1:
        return filtered[0]

    log.error("Found {num} entry/entries for {m_name}.{s_name}:".format(
        num=len(filtered), m_name=m_name, s_name=s_name))
    return None


# Validation
def check_intermodule_field(sig: OrderedDict,
                            prefix: str = "") -> Tuple[int, OrderedDict]:
    error = 0

    # type check
    if sig["type"] not in IM_TYPES:
        log.error("{prefix} Inter_signal {name} "
                  "type {type} is incorrect.".format(prefix=prefix,
                                                     name=sig["name"],
                                                     type=sig["type"]))
        error += 1

    if sig["act"] not in IM_ACTS:
        log.error("{prefix} Inter_signal {name} "
                  "act {act} is incorrect.".format(prefix=prefix,
                                                   name=sig["name"],
                                                   act=sig["act"]))
        error += 1

    # Check if type and act are matched
    if error == 0:
        if sig["act"] not in IM_VALID_TYPEACT[sig['type']]:
            log.error("{type} and {act} of {name} are not a valid pair."
                      "".format(type=sig['type'],
                                act=sig['act'],
                                name=sig['name']))
            error += 1
    # Check 'width' field
    width = 1
    if "width" not in sig:
        sig["width"] = 1
    elif not isinstance(sig["width"], int):
        width, err = check_int(sig["width"], sig["name"])
        if err:
            log.error("{prefix} Inter-module {inst}.{sig} 'width' "
                      "should be int type.".format(prefix=prefix,
                                                   inst=sig["inst_name"],
                                                   sig=sig["name"]))
            error += 1
        else:
            # convert to int value
            sig["width"] = width

    # Add empty string if no explicit default for dangling pins is given.
    # In that case, dangling pins of type struct will be tied to the default
    # parameter in the corresponding package, and dangling pins of type logic
    # will be tied off to '0.
    if "default" not in sig:
        sig["default"] = ""

    if "package" not in sig:
        sig["package"] = ""

    return error, sig


def find_otherside_modules(topcfg: OrderedDict, m,
                           s) -> List[Tuple[str, str, str]]:
    """Find far-end port based on given module and signal name
    """
    # TODO: handle special cases
    special_inst_names = {
        ('main', 'tl_rom'): ('tl_adapter_rom', 'tl'),
        ('main', 'tl_ram_main'): ('tl_adapter_ram_main', 'tl'),
        ('main', 'tl_eflash'): ('tl_adapter_eflash', 'tl'),
        ('peri', 'tl_ram_ret_aon'): ('tl_adapter_ram_ret_aon', 'tl'),
        ('main', 'tl_corei'): ('rv_core_ibex', 'tl_i'),
        ('main', 'tl_cored'): ('rv_core_ibex', 'tl_d'),
        ('main', 'tl_dm_sba'): ('dm_top', 'tl_h'),
        ('main', 'tl_debug_mem'): ('dm_top', 'tl_d'),
        ('peri', 'tl_ast'): ('ast', 'tl')
    }
    special_result = special_inst_names.get((m, s))
    if special_result is not None:
        return [('top', special_result[0], special_result[1])]

    signame = "{}.{}".format(m, s)
    for req, rsps in topcfg["inter_module"]["connect"].items():
        if req.startswith(signame):
            # return rsps after splitting module instance name and the port
            result = []
            for rsp in rsps:
                rsp_m, rsp_s, rsp_i = filter_index(rsp)
                result.append(('connect', rsp_m, rsp_s))
            return result

        for rsp in rsps:
            if signame == rsp:
                req_m, req_s, req_i = filter_index(req)
                return [('connect', req_m, req_s)]

    # if reaches here, it means either the format is wrong, or floating port.
    log.error("`find_otherside_modules()`: "
              "No such signal {}.{} exists.".format(m, s))
    return []


def check_intermodule(topcfg: Dict, prefix: str) -> int:
    if "inter_module" not in topcfg:
        return 0

    total_error = 0

    for req, rsps in topcfg["inter_module"]["connect"].items():
        error = 0
        # checking the key, value are in correct format
        # Allowed format
        #   1. module.signal
        #   2. module.signal[index] // Remember array is not yet supported
        #                           // But allow in format checker
        #
        # Example:
        #   inter_module: {
        #     'connect': {
        #       'flash_ctrl.flash': ['eflash.flash_ctrl'],
        #       'life_cycle.provision': ['debug_tap.dbg_en', 'dft_ctrl.en'],
        #       'otp.pwr_hold': ['pwrmgr.peri[0]'],
        #       'flash_ctrl.pwr_hold': ['pwrmgr.peri[1]'],
        #     }
        #   }
        #
        # If length of value list is > 1, then key should be array (width need to match)
        # If key is format #2, then length of value list shall be 1
        # If one of the value is format #2, then the key should be 1 bit width and
        # entries of value list should be 1
        req_m, req_s, req_i = filter_index(req)

        if req_s == "":
            log.error(
                "Cannot parse the inter-module signal key '{req}'".format(
                    req=req))
            error += 1

        # Check rsps signal format is list
        if not isinstance(rsps, list):
            log.error("Value of key '{req}' should be a list".format(req=req))
            error += 1
            continue

        req_struct = find_intermodule_signal(topcfg["inter_signal"]["signals"],
                                             req_m, req_s)

        err, req_struct = check_intermodule_field(req_struct)
        error += err

        if req_i != -1 and len(rsps) != 1:
            # Array format should have one entry
            log.error(
                "If key {req} has index, only one entry is allowed.".format(
                    req=req))
            error += 1

        total_width = 0
        widths = []

        # Check rsp format
        for i, rsp in enumerate(rsps):
            rsp_m, rsp_s, rsp_i = filter_index(rsp)
            if rsp_s == "":
                log.error(
                    "Cannot parse the inter-module signal key '{req}->{rsp}'".
                    format(req=req, rsp=rsp))
                error += 1

            rsp_struct = find_intermodule_signal(
                topcfg["inter_signal"]["signals"], rsp_m, rsp_s)

            err, rsp_struct = check_intermodule_field(rsp_struct)
            error += err

            total_width += rsp_struct["width"]
            widths.append(rsp_struct["width"])

            # Type check
            # If no package was declared, it is declared with an empty string
            if not rsp_struct["package"]:
                rsp_struct["package"] = req_struct.get("package", "")
            elif req_struct["package"] != rsp_struct["package"]:
                log.error(
                    "Inter-module package should be matched: "
                    "{req}->{rsp} exp({expected}), actual({actual})".format(
                        req=req_struct["name"],
                        rsp=rsp_struct["name"],
                        expected=req_struct["package"],
                        actual=rsp_struct["package"]))
                error += 1
            if req_struct["type"] != rsp_struct["type"]:
                log.error(
                    "Inter-module type should be matched: "
                    "{req}->{rsp} exp({expected}), actual({actual})".format(
                        req=req_struct["name"],
                        rsp=rsp_struct["name"],
                        expected=req_struct["type"],
                        actual=rsp_struct["type"]))
                error += 1

            # If len(rsps) is 1, then the width should be matched to req
            if req_struct["width"] != 1:
                if rsp_struct["width"] not in [1, req_struct["width"]]:
                    log.error(
                        "If req {req} is an array, "
                        "rsp {rsp} shall be non-array or array with same width"
                        .format(req=req, rsp=rsp))
                    error += 1

                elif rsp_i != -1:
                    # If rsp has index, req should be width 1
                    log.error(
                        "If rsp {rsp} has an array index, only one-to-one map is allowed."
                        .format(rsp=rsp))
                    error += 1

        # Determine if broadcast or one-to-N
        log.debug("Handling inter-sig {} {}".format(req_struct['name'], total_width))
        req_struct["end_idx"] = -1
        if req_struct["width"] > 1 or len(rsps) != 1:
            # If req width is same to the every width of rsps ==> broadcast
            if len(rsps) * [req_struct["width"]] == widths:
                log.debug("broadcast type")
                req_struct["top_type"] = "broadcast"

            # If req width is same as total width of rsps ==> one-to-N
            elif req_struct["width"] == total_width:
                log.debug("one-to-N type")
                req_struct["top_type"] = "one-to-N"

            # one-to-N connection is not fully populated
            elif req_struct["width"] > total_width:
                log.debug("partial one-to-N type")
                req_struct["top_type"] = "partial-one-to-N"
                req_struct["end_idx"] = len(rsps)

            # If not, error
            else:
                log.error("'uni' type connection {req} should be either "
                          "OneToN or Broadcast".format(req=req))
                error += 1

        elif req_struct["type"] == "uni":
            # one-to-one connection
            req_struct["top_type"] = "broadcast"

        # If req is array, it is not allowed to have partial connections.
        # Doing for loop again here: Make code separate from other checker
        # for easier maintenance
        total_error += error

        if error != 0:
            # Skip the check
            continue

    for item in topcfg["inter_module"]["top"] + list(
            topcfg["inter_module"]["external"].keys()):
        sig_m, sig_s, sig_i = filter_index(item)
        if sig_i != -1:
            log.error("{item} cannot have index".format(item=item))
            total_error += 1

        sig_struct = find_intermodule_signal(topcfg["inter_signal"]["signals"],
                                             sig_m, sig_s)
        err, sig_struct = check_intermodule_field(sig_struct)
        total_error += err

    return total_error


# Template functions
def im_defname(obj: OrderedDict) -> str:
    """return definition struct name

    e.g. flash_ctrl::flash_req_t
    """
    if obj["package"] == "":
        # should be logic
        return "logic"

    return "{package}::{struct}_t".format(package=obj["package"],
                                          struct=obj["struct"])


def im_netname(sig: OrderedDict,
               suffix: str = "", default_name=False) -> str:
    """return top signal name with index

    It also adds suffix for external signal.

    The default name input forces function to return default name, even if object
    has a connection.
    """

    # Basic check and add missing fields
    err, obj = check_intermodule_field(sig)
    assert not err

    # Floating signals
    # TODO: Find smarter way to assign default?
    if "top_signame" not in obj or default_name:
        if obj["act"] == "req" and suffix == "req":
            return ""
        if obj["act"] == "rsp" and suffix == "rsp":
            return ""
        if obj["act"] == "req" and suffix == "rsp":
            # custom default has been specified
            if obj["default"]:
                return obj["default"]
            if obj["package"] == "tlul_pkg" and obj["struct"] == "tl":
                return "{package}::{struct}_D2H_DEFAULT".format(
                    package=obj["package"], struct=obj["struct"].upper())
            return "{package}::{struct}_RSP_DEFAULT".format(
                package=obj["package"], struct=obj["struct"].upper())
        if obj["act"] == "rsp" and suffix == "req":
            # custom default has been specified
            if obj["default"]:
                return obj["default"]
            if obj.get("package") == "tlul_pkg" and obj["struct"] == "tl":
                return "{package}::{struct}_H2D_DEFAULT".format(
                    package=obj["package"], struct=obj["struct"].upper())
            # default is used for dangling ports in definitions.
            # the struct name already has `_req` suffix
            return "{package}::{struct}_REQ_DEFAULT".format(
                package=obj.get("package", ''), struct=obj["struct"].upper())
        if obj["act"] == "rcv" and suffix == "" and obj["struct"] == "logic":
            # custom default has been specified
            if obj["default"]:
                return obj["default"]
            return "'0"
        if obj["act"] == "rcv" and suffix == "":
            # custom default has been specified
            if obj["default"]:
                return obj["default"]
            return "{package}::{struct}_DEFAULT".format(
                package=obj["package"], struct=obj["struct"].upper())

        return ""

    # Connected signals
    assert suffix in ["", "req", "rsp"]

    suffix_s = "_{suffix}".format(suffix=suffix) if suffix != "" else suffix

    # External signal handling
    if "external" in obj and obj["external"]:
        pairs = {
            # act , suffix: additional suffix
            ("req", "req"): "_o",
            ("req", "rsp"): "_i",
            ("rsp", "req"): "_i",
            ("rsp", "rsp"): "_o",
            ("req", ""): "_o",
            ("rcv", ""): "_i"
        }
        suffix_s += pairs[(obj['act'], suffix)]

    return "{top_signame}{suffix}{index}".format(
        top_signame=obj["top_signame"],
        suffix=suffix_s,
        index=lib.index(obj["index"]))


def im_portname(obj: OrderedDict, suffix: str = "") -> str:
    """return IP's port name

    e.g signame_o for requester req signal
    """
    act = obj['act']
    name = obj['name']

    if suffix == "":
        suffix_s = "_o" if act == "req" else "_i"
    elif suffix == "req":
        suffix_s = "_o" if act == "req" else "_i"
    else:
        suffix_s = "_o" if act == "rsp" else "_i"

    return name + suffix_s


def get_dangling_im_def(objs: OrderedDict) -> str:
    """return partial inter-module definitions

    Dangling intermodule connections happen when a one-to-N assignment
    is not fully populated.

    This can result in two types of dangling:
    - outgoing requests not used
    - incoming responses not driven

    The determination of which category we fall into follows similar rules
    as those used by im_netname.

    When the direction of the net is the same as the active direction of the
    the connecting module, it is "unused".

    When the direction of the net is opposite of the active direction of the
    the connecting module, it is "undriven".

    As an example, edn is defined as "rsp" of a "req_rsp" pair. It is also used
    as the "active" module in inter-module connection. If there are not enough
    connecting modules, the 'req' line is undriven, while the 'rsp' line is
    unused.

    """
    unused_def = [obj for obj in objs if obj['end_idx'] > 0 and
                  obj['act'] == obj['suffix']]

    undriven_def = [obj for obj in objs if obj['end_idx'] > 0 and
                    (obj['act'] == 'req' and obj['suffix'] == 'rsp' or
                     obj['act'] == 'rsp' and obj['suffix'] == 'req')]

    return unused_def, undriven_def
