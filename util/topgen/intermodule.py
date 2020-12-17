# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import re
from collections import OrderedDict
from enum import Enum
from typing import Dict, List, Tuple

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


def get_suffixes(ims: OrderedDict) -> (str, str):
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


def autoconnect_xbar(topcfg: OrderedDict, xbar: OrderedDict):
    ports = [x for x in xbar["nodes"] if x["type"] in ["host", "device"]]
    for port in ports:
        if port["xbar"]:
            if port["type"] == "host":
                # Skip as device will add connection
                continue

            # Device port adds signal
            add_intermodule_connection(obj=topcfg,
                                       req_m=xbar["name"],
                                       req_s="tl_%s" % port["name"],
                                       rsp_m=port["name"],
                                       rsp_s="tl_%s" % xbar["name"])
            continue  # xbar port case

        # check if name exists in ["module", "memory"]
        ips = [
            x for x in topcfg["module"] + topcfg["memory"]
            if x["name"] == port["name"]
        ]

        assert len(ips) <= 1

        if len(ips) == 0:
            # if not in module, memory, should be existed in top or ext field
            module_key = "{}.tl_{}".format(xbar["name"], port["name"])
            if module_key not in topcfg["inter_module"]["top"] + list(
                    topcfg["inter_module"]["external"].keys()):
                log.error("Inter-module key {} cannot be found in module, "
                          "memory, top, or external lists.".format(module_key))
            continue

        ip = ips[0]

        # get the port name
        def get_signame(ip: OrderedDict, package: str, struct: str,
                        act: str) -> OrderedDict:
            ims = [
                x for x in ip["inter_signal_list"]
                if (x['package'] == package if 'package' in x else False) and
                x['struct'] == struct and x['act'] == act
            ]
            return ims

        if port["type"] == "device":
            ims = get_signame(ip, "tlul_pkg", "tl", "rsp")
        else:  # host type
            ims = get_signame(ip, "tlul_pkg", "tl", "req")

        assert len(ims) == 1
        sig_name = ims[0]["name"]

        add_intermodule_connection(obj=topcfg,
                                   req_m=port["name"],
                                   req_s=sig_name,
                                   rsp_m=xbar["name"],
                                   rsp_s="tl_%s" % port["name"])
        continue  # len() == 1


def autoconnect(topcfg: OrderedDict):
    """Matching the connection based on the naming rule
    between {memory, module} <-> Xbar.
    """

    # Add xbar connection to the modules, memories
    for xbar in topcfg["xbar"]:
        autoconnect_xbar(topcfg, xbar)


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
        topcfg["host"]

    intermodule_instances = [x for x in instances if "inter_signal_list" in x]

    for x in intermodule_instances:
        for sig in x["inter_signal_list"]:
            # Add instance name to the entry and add to list_of_intersignals
            sig["inst_name"] = x["name"]
            list_of_intersignals.append(sig)

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

        rsp_len = len(rsps)
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
            # Add two definitions
            definitions.append(
                OrderedDict([('package', package),
                             ('struct', req_struct["struct"] + req_suffix),
                             ('signame', sig_name + "_req"),
                             ('width', req_struct["width"]),
                             ('type', req_struct["type"]),
                             ('default', req_struct["default"])]))
            definitions.append(
                OrderedDict([('package', package),
                             ('struct', req_struct["struct"] + rsp_suffix),
                             ('signame', sig_name + "_rsp"),
                             ('width', req_struct["width"]),
                             ('type', req_struct["type"]),
                             ('default', req_struct["default"])]))
        else:
            # unidirection
            definitions.append(
                OrderedDict([('package', package),
                             ('struct', req_struct["struct"]),
                             ('signame', sig_name),
                             ('width', req_struct["width"]),
                             ('type', req_struct["type"]),
                             ('default', req_struct["default"])]))

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

            if rsp_len != 1:
                log.warning("{req}[{i}] -> {rsp}".format(req=req, i=i,
                                                         rsp=rsp))
            else:
                log.warning("{req} -> {rsp}".format(req=req, rsp=rsp))

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
                             ('default', sig["default"])]))
            definitions.append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"] + rsp_suffix),
                             ('signame', sig_name + "_rsp"),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('default', sig["default"])]))
        else:  # if sig["type"] == "uni":
            definitions.append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"]), ('signame', sig_name),
                             ('width', sig["width"]), ('type', sig["type"]),
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
        sig["top_signame"] = sig_name

        if "index" not in sig:
            sig["index"] = -1

        # Add the port definition to top external ports
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
                              'out' if sig['act'] == "req" else 'in')]))
            topcfg["inter_signal"]["external"].append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"] + rsp_suffix),
                             ('signame', sig_name + "_rsp" + rsp_sigsuffix),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('default', sig["default"]),
                             ('direction',
                              'in' if sig['act'] == "req" else 'out')]))
        else:  # uni
            if sig["act"] == "req":
                sigsuffix = "_o"
            else:
                sigsuffix = "_i"
            topcfg["inter_signal"]["external"].append(
                OrderedDict([('package', sig["package"]),
                             ('struct', sig["struct"]),
                             ('signame', sig_name + sigsuffix),
                             ('width', sig["width"]), ('type', sig["type"]),
                             ('default', sig["default"]),
                             ('direction',
                              'out' if sig['act'] == "req" else 'in')]))

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
def check_intermodule_field(obj: OrderedDict, prefix: str = "") -> int:
    error = 0

    # type check
    if obj["type"] not in IM_TYPES:
        log.error("{prefix} Inter_signal {name} "
                  "type {type} is incorrect.".format(prefix=prefix,
                                                     name=obj["name"],
                                                     type=obj["type"]))
        error += 1

    if obj["act"] not in IM_ACTS:
        log.error("{prefix} Inter_signal {name} "
                  "act {act} is incorrect.".format(prefix=prefix,
                                                   name=obj["name"],
                                                   act=obj["act"]))
        error += 1

    # Check if type and act are matched
    if error == 0:
        if obj["act"] not in IM_VALID_TYPEACT[obj['type']]:
            log.error("{type} and {act} of {name} are not a valid pair."
                      "".format(type=obj['type'],
                                act=obj['act'],
                                name=obj['name']))
            error += 1
    # Check 'width' field
    width = 1
    if "width" not in obj:
        obj["width"] = 1
    elif not isinstance(obj["width"], int):
        width, err = check_int(obj["width"], obj["name"])
        if err:
            log.error("{prefix} Inter-module {inst}.{sig} 'width' "
                      "should be int type.".format(prefix=prefix,
                                                   inst=obj["inst_name"],
                                                   sig=obj["name"]))
            error += 1
        else:
            # convert to int value
            obj["width"] = width

    # Add empty string if no explicit default for dangling pins is given.
    # In that case, dangling pins of type struct will be tied to the default
    # parameter in the corresponding package, and dangling pins of type logic
    # will be tied off to '0.
    if "default" not in obj:
        obj["default"] = ""

    return error


def find_otherside_modules(topcfg: OrderedDict, m,
                           s) -> List[Tuple[str, str, str]]:
    """Find far-end port based on given module and signal name
    """
    # TODO: handle special cases
    special_inst_names = {
        ('main', 'tl_rom'): ('tl_adapter_rom', 'tl'),
        ('main', 'tl_ram_main'): ('tl_adapter_ram_main', 'tl'),
        ('main', 'tl_eflash'): ('tl_adapter_eflash', 'tl'),
        ('peri', 'tl_ram_ret'): ('tl_adapter_ram_ret', 'tl'),
        ('main', 'tl_corei'): ('rv_core_ibex', 'tl_i'),
        ('main', 'tl_cored'): ('rv_core_ibex', 'tl_d'),
        ('main', 'tl_dm_sba'): ('dm_top', 'tl_h'),
        ('main', 'tl_debug_mem'): ('dm_top', 'tl_d'),
        ('peri', 'tl_ast_wrapper'): ('ast', 'tl')
    }
    for pair in special_inst_names:
        if pair == (m, s):
            result = special_inst_names.get(pair)
            return [('top', result[0], result[1])]

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
        # If key is format #2, then lenght of value list shall be 1
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

        error += check_intermodule_field(req_struct)

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

            error += check_intermodule_field(rsp_struct)

            total_width += rsp_struct["width"]
            widths.append(rsp_struct["width"])

            # Type check
            if "package" not in rsp_struct:
                rsp_struct["package"] = req_struct["package"]
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

        # Determine if "uni" is broadcast or one-to-N
        if req_struct["type"] == "uni" and len(rsps) != 1:
            # If req width is same as total width of rsps ==> one-to-N
            if req_struct["width"] == total_width:
                req_struct["top_type"] = "one-to-N"

            # If req width is same to the every width of rsps ==> broadcast
            elif len(rsps) * [req_struct["width"]] == widths:
                req_struct["top_type"] = "broadcast"

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
        rsps_width = 0
        for rsp in rsps:
            rsp_m, rsp_s, rsp_i = filter_index(rsp)
            rsp_struct = find_intermodule_signal(
                topcfg["inter_signal"]["signals"], rsp_m, rsp_s)
            # Update total responses width
            rsps_width += rsp_struct["width"]

        if req_struct["width"] != rsps_width:
            log.error(
                "Request {} width is not matched with total responses width {}"
                .format(req_struct["width"], rsps_width))
            error += 1

    for item in topcfg["inter_module"]["top"] + list(
            topcfg["inter_module"]["external"].keys()):
        sig_m, sig_s, sig_i = filter_index(item)
        if sig_i != -1:
            log.error("{item} cannot have index".format(item=item))
            total_error += 1
        sig_struct = find_intermodule_signal(topcfg["inter_signal"]["signals"],
                                             sig_m, sig_s)
        total_error += check_intermodule_field(sig_struct)

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


def im_netname(obj: OrderedDict, suffix: str = "") -> str:
    """return top signal name with index

    It also adds suffix for external signal
    """

    # Basic check and add missing fields
    check_intermodule_field(obj)

    # Floating signals
    # TODO: Find smarter way to assign default?
    if "top_signame" not in obj:
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
            if obj["package"] == "tlul_pkg" and obj["struct"] == "tl":
                return "{package}::{struct}_H2D_DEFAULT".format(
                    package=obj["package"], struct=obj["struct"].upper())
            return "{package}::{struct}_REQ_DEFAULT".format(
                package=obj["package"], struct=obj["struct"].upper())
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
    if suffix == "":
        suffix_s = "_o" if obj["act"] == "req" else "_i"
    elif suffix == "req":
        suffix_s = "_o" if obj["act"] == "req" else "_i"
    else:
        suffix_s = "_o" if obj["act"] == "rsp" else "_i"

    return "{signame}{suffix}".format(signame=obj["name"], suffix=suffix_s)
