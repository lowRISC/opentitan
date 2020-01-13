# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from copy import deepcopy
from functools import partial

from .lib import *
import hjson


def amend_ip(top, ip):
    """ Amend additional information into top module

    Amended fields:
        - size: register space
        - clock: converted into ip_clock
        - bus_device
        - bus_host: none if doesn't exist
        - available_input_list: empty list if doesn't exist
        - available_output_list: empty list if doesn't exist
        - available_inout_list: empty list if doesn't exist
        - interrupt_list: empty list if doesn't exist
        - alert_list: empty list if doesn't exist
    """
    ip_list_in_top = [x["name"].lower() for x in top["module"]]
    ipname = ip["name"].lower()
    if not ipname in ip_list_in_top:
        log.info("TOP doens't use the IP %s. Skip" % ip["name"])
        return

    # Find index of the IP
    ip_idx = ip_list_in_top.index(ipname)
    # Needed to detect async alert transitions below
    ah_idx = ip_list_in_top.index("alert_handler")

    ip_module = top["module"][ip_idx]

    # Size
    if not "size" in ip_module:
        ip_module["size"] = "0x%x" % max(ip["gensize"], 0x1000)
    elif ip_module["size"] < ip["gensize"]:
        log.error(
            "given 'size' field in IP %s is smaller than the required space" %
            ip_module["name"])

    # bus_device
    ip_module["bus_device"] = ip["bus_device"]

    # bus_host
    if "bus_host" in ip and ip["bus_host"] != "":
        ip_module["bus_host"] = ip["bus_host"]
    else:
        ip_module["bus_host"] = "none"

    # available_input_list , available_output_list, available_inout_list
    if "available_input_list" in ip:
        ip_module["available_input_list"] = ip["available_input_list"]
        for i in ip_module["available_input_list"]:
            i.pop('desc', None)
            i["type"] = "input"
            i["width"] = int(i["width"])
    else:
        ip_module["available_input_list"] = []
    if "available_output_list" in ip:
        ip_module["available_output_list"] = ip["available_output_list"]
        for i in ip_module["available_output_list"]:
            i.pop('desc', None)
            i["type"] = "output"
            i["width"] = int(i["width"])
    else:
        ip_module["available_output_list"] = []
    if "available_inout_list" in ip:
        ip_module["available_inout_list"] = ip["available_inout_list"]
        for i in ip_module["available_inout_list"]:
            i.pop('desc', None)
            i["type"] = "inout"
            i["width"] = int(i["width"])
    else:
        ip_module["available_inout_list"] = []

    # interrupt_list
    if "interrupt_list" in ip:
        ip_module["interrupt_list"] = ip["interrupt_list"]
        for i in ip_module["interrupt_list"]:
            i.pop('desc', None)
            i["type"] = "interrupt"
            i["width"] = int(i["width"])
    else:
        ip_module["interrupt_list"] = []

    # alert_list
    if "alert_list" in ip:
        ip_module["alert_list"] = ip["alert_list"]
        for i in ip_module["alert_list"]:
            i.pop('desc', None)
            i["type"] = "alert"
            i["width"] = int(i["width"])
            # automatically insert asynchronous transition if necessary
            if ip_module["clock_connections"]["clk_i"] == \
               top["module"][ah_idx]["clock_connections"]["clk_i"]:
                i["async"] = 0
            else:
                i["async"] = 1
    else:
        ip_module["alert_list"] = []

    # scan
    if "scan" in ip:
        ip_module["scan"] = ip["scan"]
    else:
        ip_module["scan"] = "false"


# TODO: Replace this part to be configurable from Hjson or template
predefined_modules = {
    "corei": "rv_core_ibex",
    "cored": "rv_core_ibex",
    "dm_sba": "rv_dm",
    "debug_mem": "rv_dm"
}


def is_xbar(top, name):
    """Check if the given name is crossbar
    """
    xbars = list(filter(lambda node: node["name"] == name, top["xbar"]))
    if len(xbars) == 0:
        return False, None

    if len(xbars) > 1:
        log.error("Matching crossbar {} is more than one.".format(name))
        raise SystemExit()

    return True, xbars[0]


def xbar_addhost(top, xbar, host):
    """Add host nodes information

    - xbar: bool, true if the host port is from another Xbar
    """
    # Check and fetch host if exists in nodes
    obj = list(filter(lambda node: node["name"] == host, xbar["nodes"]))
    if len(obj) == 0:
        log.warning(
            "host %s doesn't exist in the node list. Using default values" %
            host)
        obj = {
            "name": host,
            "clock": xbar['clock'],
            "reset": xbar['reset'],
            "type": "host",
            "inst_type": "",
            # The default matches RTL default
            # pipeline_byp is don't care if pipeline is false
            "pipeline": "true",
            "pipeline_byp": "true"
        }
        topxbar["nodes"].append(obj)
        return

    xbar_bool, xbar_h = is_xbar(top, host)
    if xbar_bool:
        log.info("host {} is a crossbar. Nothing to deal with.".format(host))

    obj[0]["xbar"] = xbar_bool

    if 'clock' not in obj[0]:
        obj[0]["clock"] = xbar['clock']

    if 'reset' not in obj[0]:
        obj[0]["reset"] = xbar["reset"]

    obj[0]["inst_type"] = predefined_modules[
        host] if host in predefined_modules else ""
    obj[0]["pipeline"] = obj[0]["pipeline"] if "pipeline" in obj[0] else "true"
    obj[0]["pipeline_byp"] = obj[0]["pipeline_byp"] if obj[0][
        "pipeline"] == "true" and "pipeline_byp" in obj[0] else "true"


def process_pipeline_var(node):
    """Add device nodes pipeline / pipeline_byp information

    - Supply a default of true / true if not defined by xbar
    """
    node["pipeline"] = node["pipeline"] if "pipeline" in node else "true"
    node["pipeline_byp"] = node[
        "pipeline_byp"] if "pipeline_byp" in node else "true"


def xbar_adddevice(top, xbar, device):
    """Add device nodes information

    - clock: comes from module if exist, use xbar default otherwise
    - reset: comes from module if exist, use xbar default otherwise
    - inst_type: comes from module or memory if exist.
    - base_addr: comes from module or memory, or assume rv_plic?
    - size_byte: comes from module or memory
    - xbar: bool, true if the device port is another xbar
    """
    deviceobj = list(
        filter(lambda node: node["name"] == device,
               top["module"] + top["memory"]))
    nodeobj = list(filter(lambda node: node["name"] == device, xbar["nodes"]))

    xbar_list = [x["name"] for x in top["xbar"] if x["name"] != xbar["name"]]

    # case 1: another xbar --> check in xbar list
    if device in xbar_list and len(nodeobj) == 0:
        log.error(
            "Another crossbar %s needs to be specified in the 'nodes' list" %
            device)
        return

    if len(deviceobj) == 0:
        # doesn't exist,

        # case 1: Crossbar handling
        if device in xbar_list:
            log.warning(
                "device {} in Xbar {} is connected to another Xbar".format(
                    device, xbar["name"]))
            assert len(nodeobj) == 1
            nodeobj[0]["xbar"] = True
            process_pipeline_var(nodeobj[0])
            return

        # case 2: predefined_modules (debug_mem, rv_plic)
        # TODO: Find configurable solution not from predefined but from object?
        if device in predefined_modules:
            if device == "debug_mem":
                if len(nodeobj) == 0:
                    # Add new debug_mem
                    xbar["nodes"].append({
                        "name": "debug_mem",
                        "type": "device",
                        "clock": xbar['clock'],
                        "reset": xbar['reset'],
                        "inst_type": predefined_modules["debug_mem"],
                        "addr_range": [{
                            "base_addr": top["debug_mem_base_addr"],
                            "size_byte": "0x1000",
                        }],
                        "xbar": False,
                        "pipeline" : "true",
                        "pipeline_byp" : "true"
                    }) # yapf: disable
                else:
                    # Update if exists
                    node = nodeobj[0]
                    node["inst_type"] = predefined_modules["debug_mem"]
                    node["addr_range"] = [{
                        "base_addr":
                        top["debug_mem_base_addr"],
                        "size_byte":
                        "0x1000"
                    }]
                    node["xbar"] = False
                    process_pipeline_var(node)
            else:
                log.error("device %s shouldn't be host type" % device)
                return
        # case 3: not defined
        else:
            # Crossbar check
            log.error(
                "device %s doesn't exist in 'module', 'memory', or predefined"
                % device)
            return

    # Search object from module or memory
    elif len(nodeobj) == 0:
        # found in module or memory but node object doesn't exist.
        xbar["nodes"].append({
            "name" : device,
            "type" : "device",
            "clock" : deviceobj[0]["clock"],
            "reset" : deviceobj[0]["reset"],
            "inst_type" : deviceobj[0]["type"],
            "addr_range": [{"base_addr" : deviceobj[0]["base_addr"],
                            "size_byte": deviceobj[0]["size"]}],
            "pipeline" : "true",
            "pipeline_byp" : "true",
            "xbar" : True if device in xbar_list else False
        }) # yapf: disable

    else:
        # found and exist in the nodes too
        node = nodeobj[0]
        node["inst_type"] = deviceobj[0]["type"]
        node["addr_range"] = [{
            "base_addr": deviceobj[0]["base_addr"],
            "size_byte": deviceobj[0]["size"]
        }]
        node["xbar"] = True if device in xbar_list else False
        process_pipeline_var(node)


def amend_xbar(top, xbar):
    """Amend crossbar informations to the top list

    Amended fields
    - clock: Adopt from module clock if exists
    - inst_type: Module instance some module will be hard-coded
                 the tool searches module list and memory list then put here
    - base_addr: from top["module"]
    - size: from top["module"]
    """
    xbar_list = [x["name"] for x in top["xbar"]]
    if not xbar["name"] in xbar_list:
        log.info(
            "Xbar %s doesn't belong to the top %s. Check if the xbar doesn't need"
            % (xbar["name"], top["name"]))
        return

    topxbar = list(
        filter(lambda node: node["name"] == xbar["name"], top["xbar"]))[0]

    topxbar["connections"] = deepcopy(xbar["connections"])
    if "nodes" in xbar:
        topxbar["nodes"] = deepcopy(xbar["nodes"])
    else:
        topxbar["nodes"] = []

    # xbar primary clock and reset
    topxbar["clock"] = xbar["clock_primary"]
    topxbar["reset"] = xbar["reset_primary"]

    # Build nodes from 'connections'
    device_nodes = set()
    for host, devices in xbar["connections"].items():
        # add host first
        xbar_addhost(top, topxbar, host)

        # add device if doesn't exist
        device_nodes.update(devices)

    log.info(device_nodes)
    for device in device_nodes:
        xbar_adddevice(top, topxbar, device)


def xbar_cross(xbar, xbars):
    """Check if cyclic dependency among xbars

    And gather the address range for device port (to another Xbar)

    @param node_name if not "", the function only search downstream
                     devices starting from the node_name
    @param visited   The nodes it visited to reach this port. If any
                     downstream port from node_name in visited, it means
                     circular path exists. It should be fatal error.
    """
    # Step 1: Visit devices (gather the address range)
    log.info("Processing circular path check for {}".format(xbar["name"]))
    addr = []
    for node in [
            x for x in xbar["nodes"]
            if x["type"] == "device" and "xbar" in x and x["xbar"] == False
    ]:
        addr.extend(node["addr_range"])

    # Step 2: visit xbar device ports
    xbar_nodes = [
        x for x in xbar["nodes"]
        if x["type"] == "device" and "xbar" in x and x["xbar"] == True
    ]

    # Now call function to get the device range
    # the node["name"] is used to find the host_xbar and its connection. The
    # assumption here is that there's only one connection from crossbar A to
    # crossbar B.
    #
    # device_xbar is the crossbar has a device port with name as node["name"].
    # host_xbar is the crossbar has a host port with name as node["name"].
    for node in xbar_nodes:
        xbar_addr = xbar_cross_node(node["name"], xbar, xbars, visited=[])
        node["addr_range"] = xbar_addr


def xbar_cross_node(node_name, device_xbar, xbars, visited=[]):
    # 1. Get the connected xbar
    host_xbars = [x for x in xbars if x["name"] == node_name]
    assert len(host_xbars) == 1
    host_xbar = host_xbars[0]

    log.info("Processing node {} in Xbar {}.".format(node_name,
                                                     device_xbar["name"]))
    result = []  # [(base_addr, size), .. ]
    # Sweep the devices using connections and gather the address.
    # If the device is another xbar, call recursive
    visited.append(host_xbar["name"])
    devices = host_xbar["connections"][device_xbar["name"]]

    for node in host_xbar["nodes"]:
        if not node["name"] in devices:
            continue
        if "xbar" in node and node["xbar"] == True:
            if not "addr_range" in node:
                # Deeper dive into another crossbar
                xbar_addr = xbar_cross_node(node["name"], host_xbar, xbars,
                                            visited)
                node["addr_range"] = xbar_addr

        result.extend(deepcopy(node["addr_range"]))

    visited.pop()

    return result


def amend_interrupt(top):
    """Check interrupt_module if exists, or just use all modules
    """
    if not "interrupt_module" in top:
        top["interrupt_module"] = [x["name"] for x in top["module"]]

    if not "interrupt" in top or top["interrupt"] == "":
        top["interrupt"] = []

    for m in top["interrupt_module"]:
        ip = list(filter(lambda module: module["name"] == m, top["module"]))
        if len(ip) == 0:
            log.warning(
                "Cannot find IP %s which is used in the interrupt_module" % m)
            continue

        log.info("Adding interrupts from module %s" % ip[0]["name"])
        top["interrupt"] += list(
            map(partial(add_prefix_to_signal, prefix=m.lower()),
                ip[0]["interrupt_list"]))


def amend_alert(top):
    """Check interrupt_module if exists, or just use all modules
    """
    if not "alert_module" in top:
        top["alert_module"] = [x["name"] for x in top["module"]]

    if not "alert" in top or top["alert"] == "":
        top["alert"] = []

    for m in top["alert_module"]:
        ip = list(filter(lambda module: module["name"] == m, top["module"]))
        if len(ip) == 0:
            log.warning("Cannot find IP %s which is used in the alert_module" %
                        m)
            continue

        log.info("Adding alert from module %s" % ip[0]["name"])
        top["alert"] += list(
            map(partial(add_prefix_to_signal, prefix=m.lower()),
                ip[0]["alert_list"]))


def amend_pinmux_io(top):
    """ Check dio_modules/ mio_modules. If not exists, add all modules to mio
    """
    pinmux = top["pinmux"]

    if not "dio_modules" in pinmux:
        pinmux['dio_modules'] = []

    # list out dedicated IO
    pinmux['dio'] = []
    for e in pinmux["dio_modules"]:
        # Check name if it is module or signal
        mname, sname = get_ms_name(e["name"])

        # Parse how many signals
        m = get_module_by_name(top, mname)

        if sname != None:
            signals = deepcopy([get_signal_by_name(m, sname)])
        else:
            # Get all module signals
            signals = deepcopy(m["available_input_list"] +
                               m["available_output_list"] +
                               m["available_inout_list"])

        sig_width = sum([s["width"] for s in signals])

        # convert signal with module name
        signals = list(
            map(partial(add_prefix_to_signal, prefix=mname), signals))
        # Parse how many pads are assigned
        if not "pad" in e:
            raise SystemExit("Should catch pad field in validate.py!")

        total_width = 0

        # pads are the list of individual pin, each entry is 1 bit width
        pads = []
        for p in e["pad"]:
            pads += get_pad_list(p)

        # check if #sig and #pads are matched
        if len(pads) != sig_width:
            raise SystemExit("# Pads and # Sig (%s) aren't same: %d" %
                             (mname, sig_width))

        # add info to pads["dio"]
        for s in signals:
            p = pads[:s["width"]]
            pads = pads[s["width"]:]
            s["pad"] = p
            pinmux["dio"].append(s)

    dio_names = [p["name"] for p in pinmux["dio"]]

    ## Multiplexer IO
    if not "mio_modules" in pinmux:
        # Add all modules having available io to Multiplexer IO
        pinmux["mio_modules"] = []

        for m in top["module"]:
            num_io = len(m["available_input_list"] +
                         m["available_output_list"] +
                         m["available_inout_list"])
            if num_io != 0:
                # Add if not in dio_modules
                pinmux["mio_modules"].append(m["name"])

    # List up the dedicated IO to exclude from inputs/outputs

    # Add port list to `inputs` and `outputs` fields
    if not "inputs" in pinmux:
        pinmux["inputs"] = []
    if not "outputs" in pinmux:
        pinmux["outputs"] = []
    if not "inouts" in pinmux:
        pinmux["inouts"] = []

    for e in pinmux["mio_modules"]:
        tokens = e.split('.')
        if len(tokens) not in [1, 2]:
            raise SystemExit(
                "Cannot parse signal/module in mio_modules {}".format(e))
        # Add all ports from the module to input/outputs
        m = get_module_by_name(top, tokens[0])
        if m == None:
            raise SystemExit("Module {} doesn't exist".format(tokens[0]))

        if len(tokens) == 1:
            pinmux["inputs"] += list(
                filter(
                    lambda x: x["name"] not in dio_names,
                    map(
                        partial(add_prefix_to_signal,
                                prefix=m["name"].lower()),
                        m["available_input_list"])))
            pinmux["outputs"] += list(
                filter(
                    lambda x: x["name"] not in dio_names,
                    map(
                        partial(add_prefix_to_signal,
                                prefix=m["name"].lower()),
                        m["available_output_list"])))
            pinmux["inouts"] += list(
                filter(
                    lambda x: x["name"] not in dio_names,
                    map(
                        partial(add_prefix_to_signal,
                                prefix=m["name"].lower()),
                        m["available_inout_list"])))

        elif len(tokens) == 2:
            # Current version doesn't consider signal in mio_modules
            # only in dio_modules
            raise SystemExit(
                "Curren version doesn't support signal in mio_modules {}".
                format(e))


def merge_top(topcfg, ipobjs, xbarobjs):
    gencfg = deepcopy(topcfg)

    # Combine ip cfg into topcfg
    for ip in ipobjs:
        amend_ip(gencfg, ip)

    # Combine the interrupt (should be processed prior to xbar)
    amend_interrupt(gencfg)

    # Combine the alert (should be processed prior to xbar)
    amend_alert(gencfg)

    # Creates input/output list in the pinmux
    log.info("Processing PINMUX")
    amend_pinmux_io(gencfg)

    # Combine xbar into topcfg
    for xbar in xbarobjs:
        amend_xbar(gencfg, xbar)

    # 2nd phase of xbar (gathering the devices address range)
    for xbar in gencfg["xbar"]:
        xbar_cross(xbar, gencfg["xbar"])

    # remove unwanted fields 'debug_mem_base_addr'
    gencfg.pop('debug_mem_base_addr', None)

    return gencfg
