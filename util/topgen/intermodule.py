# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
import logging as log
from typing import Dict, Tuple
from collections import OrderedDict

from .lib import *

from reggen.validate import check_int


def intersignal_format(uid: int, req: Dict, rsp: Dict) -> str:
    """Determine the signal format of the inter-module connections

    @param[uid] Unique ID. Each inter-signal has its own ID at top

    @param[req] Request struct. It has instance name, package format
                and etc.

    @param[rsp] Response struct. Same format as @param[req]
    """

    # TODO: Handle array signal
    result = "{req}_{rsp}_{struct}".format(req=req["inst_name"],
                                           rsp=rsp["inst_name"],
                                           struct=req["struct"])

    # check signal length if exceeds 100

    # 7 : space + .
    # 3 : _{i|o}(
    # 6 : _{req|rsp}),
    req_length = 7 + len(req["name"]) + 3 + len(result) + 6
    rsp_length = 7 + len(rsp["name"]) + 3 + len(result) + 6

    if max(req_length, rsp_length) > 100:
        logmsg = "signal {0} length cannot be greater than 100"
        log.warning(logmsg.format(result))
        log.warning("Please consider shorten the instance name")
    return result


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
    instances = topcfg["module"] + topcfg["memory"]

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
    assert error is 0, "Inter-module validation is failed cannot move forward."

    # intermodule
    definitions = []

    uid = 0  # Unique connection ID across the top

    # inter_module: {
    #   // template 1
    #   'flash_ctrl.flash': ['eflash.flash_ctrl']
    #   // template 2
    #   'module_a.sig_a' : ['module_b.sig_a', 'module_c.sig_a[0]']
    # },
    for req, rsps in topcfg["inter_module"].items():
        log.info("{req} --> {rsps}".format(req=req, rsps=rsps))

        # Split index
        req_module, req_signal, req_index = filter_index(req)

        # get the module signal
        req_struct = find_intermodule_signal(list_of_intersignals, req_module,
                                             req_signal)

        rsp_len = len(rsps)
        for i, rsp in enumerate(rsps):
            assert i == 0, "Handling multiple connections (array) isn't yet supported"

            # Split index
            rsp_module, rsp_signal, rsp_index = filter_index(rsp)

            rsp_struct = find_intermodule_signal(list_of_intersignals,
                                                 rsp_module, rsp_signal)

            # determine the signal name
            sig_name = "im{uid}_{req_s}".format(uid=uid,
                                                req_s=req_struct['struct'])
            sig_name = intersignal_format(uid, req_struct, rsp_struct)

            req_struct["top_signame"] = sig_name
            rsp_struct["top_signame"] = sig_name

            # Add to definitions
            if "package" in req_struct:
                package = req_struct["package"]
            elif "package" in rsp_struct:
                package = rsp_struct["package"]
            else:
                package = ""

            # Assume it is logic
            # req_rsp doesn't allow logic
            if req_struct["struct"] is "logic":
                assert req_struct[
                    "type"] is not "req_rsp", "logic signal cannot have req_rsp type"
            definitions.append(
                OrderedDict([('package', package),
                             ('struct', req_struct["struct"]),
                             ('signame', sig_name),
                             ('width', req_struct["width"]),
                             ('type', req_struct["type"])]))

            if rsp_len != 1:
                log.warning("{req}[{i}] -> {rsp}".format(req=req, i=i,
                                                         rsp=rsp))
            else:
                log.warning("{req} -> {rsp}".format(req=req, rsp=rsp))

            # increase Unique ID
            uid += 1

    # TODO: Check unconnected port

    for sig in topcfg["inter_signal"]["signals"]:
        # Check if it exist in definitions
        if "top_signame" in sig:
            continue

        # Handle the unconnected port rule

        # Option #1: tied the default value

        # Option #2: External port (TBD)

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

    return filtered[0] if len(filtered) == 1 else None


## Validation
def check_intermodule(topcfg: Dict, prefix: str) -> int:
    if "inter_module" not in topcfg:
        return 0

    total_error = 0

    for req, rsps in topcfg["inter_module"].items():
        error = 0
        # checking the key, value are in correct format
        # Allowed format
        #   1. module.signal
        #   2. module.signal[index] // Remember array is not yet supported
        #                           // But allow in format checker
        #
        # Example:
        #   inter_module: {
        #     'flash_ctrl.flash': ['eflash.flash_ctrl'],
        #     'life_cycle.provision': ['debug_tap.dbg_en', 'dft_ctrl.en'],
        #     'otp.pwr_hold': ['pwrmgr.peri[0]'],
        #     'flash_ctrl.pwr_hold': ['pwrmgr.peri[1]'],
        #   }
        #
        # If length of value list is > 1, then key should be array (width need to match)
        # If key is format #2, then lenght of value list shall be 1
        # If one of the value is format #2, then the key should be 1 bit width and
        # entries of value list should be 1
        req_m, req_s, req_i = filter_index(req)

        if req_s is "":
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

        # Check 'width' field
        if "width" not in req_struct:
            req_struct["width"] = 1
        elif not isinstance(req_struct["width"], int):
            width, err = check_int(req_struct["width"], req_struct["name"])
            if err:
                log.error(
                    "Inter-module {inst}.{sig} 'width' should be int type.".
                    format(inst=req_struct["inst_name"],
                           sig=req_struct["name"]))
                error += 1
            else:
                # convert to int value
                req_struct["width"] = width

        if req_i != -1 and len(rsps) != 1:
            # Array format should have one entry
            log.error(
                "If key {req} has index, only one entry is allowed.".format(
                    req=req))
            error += 1

        # Check rsp format
        for i, rsp in enumerate(rsps):
            rsp_m, rsp_s, rsp_i = filter_index(rsp)
            if rsp_s is "":
                log.error(
                    "Cannot parse the inter-module signal key '{req}->{rsp}'".
                    format(req=req, rsp=rsp))
                error += 1

            rsp_struct = find_intermodule_signal(
                topcfg["inter_signal"]["signals"], rsp_m, rsp_s)

            # Check 'width' field
            width = 1
            if "width" not in rsp_struct:
                rsp_struct["width"] = 1
            elif not isinstance(rsp_struct["width"], int):
                width, err = check_int(rsp_struct["width"], rsp_struct["name"])
                if err:
                    log.error(
                        "Inter-module {inst}.{sig} 'width' should be int type."
                        .format(inst=rsp_struct["inst_name"],
                                sig=rsp_struct["name"]))
                    error += 1
                else:
                    # convert to int value
                    rsp_struct["width"] = width

            if req_struct["width"] != 1:
                if width not in [1, req_struct["width"]]:
                    log.error(
                        "If req {req} is an array, rsp {rsp} shall be non-array or array with same width"
                        .format(req=req, rsp=rsp))
                    error += 1

                elif rsp_i != -1:
                    # If rsp has index, req should be width 1
                    log.error(
                        "If rsp {rsp} has an array index, only one-to-one map is allowed."
                        .format(rsp=rsp))
                    error += 1

        # All rsps are checked, check the total width to req width
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

    return total_error
