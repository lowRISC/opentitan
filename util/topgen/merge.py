# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from copy import deepcopy
from pathlib import Path, PosixPath

import hjson

def get_n_format_value (key, default, inst):
    inst_list = []
    error = 0
    if key not in inst.keys():
        inst_list.append(default)
    elif isinstance(inst[key], str):
        inst_list.append(inst[key])
    elif isinstance(inst[key], list):
        inst_list.extend(inst[key])
    else:
        log.error("definition in %s hjson is incorrect" % inst['name'])
        error += 1

    return error, inst_list

def create_clk_map(top, inst):
    # create list of clock port to clock net mapping
    clock_connections = {}
    error = 0

    # Gather clock port names from IP
    derr, inst_clocks = get_n_format_value('clock_primary', 'clk_i', inst)
    error += derr

    if 'other_clock_list' in inst.keys():
        inst_clocks.extend(inst['other_clock_list'])

    # Match with top level clocks
    derr, clock_nets = get_n_format_value('clock', top['name'], top)

    if len(inst_clocks) != len(clock_nets):
        log.error("The number of clock ports / clock nets for module %s do not match" % top['name'])
        error += 1
        return error

    for i in range(len(inst_clocks)):
        port_name = "clk_i" if inst_clocks[i] == 'main' else inst_clocks[i]
        clock_connections[port_name] = clock_nets[i]

    return error, clock_connections

def create_reset_map(top, inst):

    reset_connectivity = {}
    error = 0

    if 'reset' not in top:
        top['reset'] = [top['name']]
    elif isinstance(top['reset'] , str):
        top['reset'] = [top['reset']]

    if not isinstance(top['reset'] , list):
        log.error("Reset nets must be defined as a list")
        error += 1

    # gather IP reset ports
    # if ports defined already, use them
    # if not, declare a default rst_ni port
    inst_resets = []
    if "reset" in inst:
        if isinstance(inst['reset'] , str):
            inst_resets.extend([inst['reset']])
        else:
            inst_resets.extend(inst['reset'])
    else:
        inst_resets.extend(["rst_ni"])

    if len(inst_resets) != len(top["reset"]):
        log.error("The number of reset ports / reset nets for module %s do not match" % top['name'])
        error += 1

    for i in range(len(inst_resets)):
        reset_connectivity[inst_resets[i]] = top['reset'][i]

    return error, reset_connectivity

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
    p = ip_path.glob('*/doc/*.hjson')

    # filter only ip_name/doc/ip_name{_reg|''}.hjson
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


def amend_mem(mem):
    """ Amend additional memory information into top module

    Amended fields:
        - reset: assign reset if one is not created
    """

    error, mem['reset_connectivity'] = create_reset_map(mem, [])
    error, mem['clock_connections'] = create_clk_map(mem, {})


def amend_ip(top, ip):
    """ Amend additional information into top module

    Amended fields:
        - size: register space
        - clock: converted into ip_clock
        - reset: set of {reset_port : top_level_reset_net} mappings
                 reset_port is obtained from ip.hjson, default is rst_ni
                 reset net attributes is defined in top_*.hjson
        - bus_device
        - bus_host: none if doesn't exist
        - available_input_list: empty list if doesn't exist
        - available_output_list: empty list if doesn't exist
        - available_inout_list: empty list if doesn't exist
        - interrupt_list: empty list if doesn't exist
        - (TBD) alert_list: empty list if doesn't exist
    """
    ip_list_in_top = [x["name"].lower() for x in top["module"]]
    ipname = ip["name"].lower()
    if not ipname in ip_list_in_top:
        log.info("TOP doens't use the IP %s. Skip" % ip["name"])
        return

    # Find index of the IP
    ip_idx = ip_list_in_top.index(ipname)

    ip_module = top["module"][ip_idx]

    # Size
    if not "size" in ip_module:
        ip_module["size"] = "0x%x" % max(ip["gensize"], 0x1000)
    elif ip_module["size"] < ip["gensize"]:
        log.error(
            "given 'size' field in IP %s is smaller than the required space" %
            ip_module["name"])

    error = 0
    err, ip_module['clock_connections'] = create_clk_map(ip_module, ip)
    error += err

    # create list of reset port to reset net mapping
    err, ip_module['reset_connectivity'] = create_reset_map(ip_module, ip)
    error += err

    if error:
        return

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
            i["width"] = int(i["width"])
    else:
        ip_module["available_input_list"] = []
    if "available_output_list" in ip:
        ip_module["available_output_list"] = ip["available_output_list"]
        for i in ip_module["available_output_list"]:
            i.pop('desc', None)
            i["width"] = int(i["width"])
    else:
        ip_module["available_output_list"] = []
    if "available_inout_list" in ip:
        ip_module["available_inout_list"] = ip["available_inout_list"]
        for i in ip_module["available_inout_list"]:
            i.pop('desc', None)
            i["width"] = int(i["width"])
    else:
        ip_module["available_inout_list"] = []

    # interrupt_list
    if "interrupt_list" in ip:
        ip_module["interrupt_list"] = ip["interrupt_list"]
        for i in ip_module["interrupt_list"]:
            i.pop('desc', None)
            i["width"] = int(i["width"])
    else:
        ip_module["interrupt_list"] = []

    # (TBD) alert_list

    # scan
    if "scan" in ip:
        ip_module["scan"] = ip["scan"]
    else:
        ip_module["scan"] = "false"


# TODO: Replace this part to be configurable from hjson or template
predefined_modules = {
    "corei": "rv_core_ibex",
    "cored": "rv_core_ibex",
    "dm_sba": "rv_dm",
    "debug_mem": "rv_dm"
}


def xbar_addhost(xbar, host):
    # TODO: check if host is another crossbar
    # Check and fetch host if exists in nodes
    obj = list(filter(lambda node: node["name"] == host, xbar["nodes"]))
    if len(obj) == 0:
        log.warning(
            "host %s doesn't exist in the node list. Using default values" %
            host)
        obj = {
            "name": host,
            "clock": xbar["clock"],
            "reset": xbar["reset"][0],
            "type": "host",
            "inst_type": "",
            # The default matches RTL default
            # pipeline_byp is don't care if pipeline is false
            "pipeline": "true",
            "pipeline_byp": "true"
        }
        topxbar["nodes"].append(obj)
    else:
        obj[0]["clock"] = xbar["clock"]
        obj[0]["reset"] = xbar["reset"][0]
        obj[0]["inst_type"] = predefined_modules[
            host] if host in predefined_modules else ""
        obj[0]["pipeline"] = obj[0]["pipeline"] if "pipeline" in obj[
            0] else "true"
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

    - clock: comes from module if exist. use main top clock for memory as of now
    - reset: if defined, reuse existing definiton, otherwise use xbar reset
    - inst_type: comes from module or memory if exist.
    - base_addr: comes from module or memory, or assume rv_plic?
    - size_byte: comes from module or memory
    """
    deviceobj = list(
        filter(lambda node: node["name"] == device,
               top["module"] + top["memory"]))
    nodeobj = list(filter(lambda node: node["name"] == device, xbar["nodes"]))

    xbar_list = [x["name"] for x in top["xbar"] if x["name"] != xbar["name"]]

    if len(deviceobj) == 0:
        # doesn't exist,
        # case 1: another xbar --> check in xbar list
        if device in xbar_list and len(nodeobj) == 0:
            log.error(
                "Another crossbar %s needs to be specified in the 'nodes' list"
                % device)
            return

        # case 2: predefined_modules (debug_mem, rv_plic)
        # TODO: Find configurable solution not from predefined but from object?
        elif device in predefined_modules:
            if device == "debug_mem":
                if len(nodeobj) == 0:
                    # Add new debug_mem
                    xbar["nodes"].append({
                        "name": "debug_mem",
                        "type": "device",
                        "clock": "main",
                        "reset": xbar['reset'][0],
                        "inst_type": predefined_modules["debug_mem"],
                        "base_addr": top["debug_mem_base_addr"],
                        "size_byte": "0x1000",
                        "pipeline" : "true",
                        "pipeline_byp" : "true"
                    }) # yapf: disable
                else:
                    # Update if exists
                    node = nodeobj[0]
                    node["reset"] = xbar['reset'][0] if 'reset' not in node else node['reset']
                    node["inst_type"] = predefined_modules["debug_mem"]
                    node["base_addr"] = top["debug_mem_base_addr"]
                    node["size_byte"] = "0x1000"
                    process_pipeline_var(node)
            else:
                log.error("device %s shouldn't be host type" % device)
                return
        # case 3: not defined
        else:
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
            "reset" : xbar['reset'][0],
            "inst_type" : deviceobj[0]["type"],
            "base_addr" : deviceobj[0]["base_addr"],
            "size_byte": deviceobj[0]["size"],
            "pipeline" : "true",
            "pipeline_byp" : "true"
        }) # yapf: disable

    else:
        # found and exist in the nodes too
        node = nodeobj[0]
        node["reset"] = xbar['reset'][0] if 'reset' not in node else node['reset']
        node["inst_type"] = deviceobj[0]["type"]
        node["base_addr"] = deviceobj[0]["base_addr"]
        node["size_byte"] = deviceobj[0]["size"]
        process_pipeline_var(node)


def amend_xbar(top, xbar):
    """Amend crossbar informations to the top list

    Amended fields
    - clock: Adopt from module clock if exists
    - reset: If not defined, create a default one
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

    # create list of reset port to reset net mapping
    error = 0
    err, topxbar['clock_connections'] = create_clk_map(topxbar, xbar)
    error += err

    err, topxbar['reset_connectivity'] = create_reset_map(topxbar, xbar)
    error += err

    if error:
        return

    # Build nodes from 'connections'
    device_nodes = set()
    for host, devices in xbar["connections"].items():
        # add host first
        xbar_addhost(topxbar, host)

        # add device if doesn't exist
        device_nodes.update(devices)

    log.info(device_nodes)
    for device in device_nodes:
        xbar_adddevice(top, topxbar, device)


def prefix_module(module, interrupt_list):
    result = []
    for i in interrupt_list:
        result.append({
            "name": module.lower() + "_" + i["name"],
            "width": i["width"]
        })

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
        top["interrupt"] += prefix_module(m, ip[0]["interrupt_list"])


def merge_top(topcfg, ipobjs, xbarobjs):
    gencfg = deepcopy(topcfg)

    # Primarily create clocks/resets if not present
    mem_objs = gencfg['memory'] if 'memory' in gencfg.keys() else []
    for mem in mem_objs:
        amend_mem(mem)

    # Combine ip cfg into topcfg
    for ip in ipobjs:
        amend_ip(gencfg, ip)

    # Combine the interrupt (should be processed prior to xbar)
    amend_interrupt(gencfg)

    # Combine xbar into topcfg
    for xbar in xbarobjs:
        amend_xbar(gencfg, xbar)

    # remove unwanted fields 'debug_mem_base_addr'
    gencfg.pop('debug_mem_base_addr', None)

    # validate resets

    return gencfg
