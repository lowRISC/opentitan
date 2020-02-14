# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from typing import Dict

from .lib import *


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


def elab_intermodule(topcfg):
    """Check the connection of inter-module and categorize them

    In the top template, it uses updated inter_module fields to create
    connections between the modules (incl. memories). This function is to
    create and check the validity of the connections `inter_module` using IPs'
    `inter_signal_list`.
    """

    list_of_intersignals = []

    if "inter_signal" not in topcfg:
        topcfg["inter_signal"] = {}

    # Gather the inter_signal_list
    instances = topcfg["module"] + topcfg["memory"]

    intermodule_instances = [x for x in instances if "inter_signal_list" in x]

    for x in intermodule_instances:
        for sig in x["inter_signal_list"]:
            # Add instance name to the entry and add to list_of_intersignals
            sig["inst_name"] = x["name"]
            list_of_intersignals.append(sig)

    # TODO: Cross check

    # Add field to the topcfg
    topcfg["inter_signal"]["signals"] = list_of_intersignals

    # intermodule
    definitions = []

    uid = 0  # Unique connection ID across the top

    for req, rsps in topcfg["inter_module"].items():
        log.info("{req} --> {rsps}".format(req=req, rsps=rsps))
        req_module, req_signal = req.split('.')

        # get the module signal
        req_struct = find_intermodule_signal(list_of_intersignals, req_module,
                                             req_signal)

        rsp_len = len(rsps)
        for i, rsp in enumerate(rsps):
            assert i == 0, "Handling multiple connections (array) isn't yet supported"
            rsp_module, rsp_signal = rsp.split('.')

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
            else:
                assert "package" in rsp_struct, "Either req/rsp shall have 'package' field"
                package = rsp_struct["package"]

            definitions.append({
                'package': package,
                'struct': req_struct["struct"],
                'signame': sig_name,
                'type': req_struct["type"]
            })

            if rsp_len != 1:
                log.warning("{req}[{i}] -> {rsp}".format(req=req, i=i,
                                                         rsp=rsp))
            else:
                log.warning("{req} -> {rsp}".format(req=req, rsp=rsp))

            # increase Unique ID
            uid += 1

    # TODO: Check unconnected port

    if "definitions" not in topcfg["inter_signal"]:
        topcfg["inter_signal"]["definitions"] = definitions


def find_intermodule_signal(sig_list, m_name, s_name) -> Dict:
    """Return the intermodule signal structure
    """

    filtered = [
        x for x in sig_list if x["name"] == s_name and x["inst_name"] == m_name
    ]

    assert len(
        filtered
    ) == 1, "Error on finding the inter module signal {m_name}.{s_name}".format(
        m_name=m_name, s_name=s_name)

    return filtered[0]
