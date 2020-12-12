# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import random
from collections import OrderedDict
from copy import deepcopy
from functools import partial
from math import ceil, log2

from topgen import c, lib


def _get_random_data_hex_literal(width):
    """ Fetch 'width' random bits and return them as hex literal"""
    width = int(width)
    literal_str = hex(random.getrandbits(width))
    return literal_str


def _get_random_perm_hex_literal(numel):
    """ Compute a random permutation of 'numel' elements and
    return as packed hex literal"""
    num_elements = int(numel)
    width = int(ceil(log2(num_elements)))
    idx = [x for x in range(num_elements)]
    random.shuffle(idx)
    literal_str = ""
    for k in idx:
        literal_str += format(k, '0' + str(width) + 'b')
    # convert to hex for space efficiency
    literal_str = hex(int(literal_str, 2))
    return literal_str


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
        - param_list: empty list if doesn't exist
        - interrupt_list: empty list if doesn't exist
        - alert_list: empty list if doesn't exist
        - wakeup_list: empty list if doesn't exist
    """
    ip_list_in_top = [x["type"].lower() for x in top["module"]]
    # TODO make set
    ipname = ip["name"].lower()
    if ipname not in ip_list_in_top:
        log.info("TOP doens't use the IP %s. Skip" % ip["name"])
        return

    # Initialize RNG for compile-time netlist constants.
    random.seed(int(top['rnd_cnst_seed']))

    # Needed to detect async alert transitions below
    ah_idx = ip_list_in_top.index("alert_handler")

    # Find multiple IPs
    # Find index of the IP
    ip_modules = list(
        filter(lambda module: module["type"] == ipname, top["module"]))

    for ip_module in ip_modules:
        mod_name = ip_module["name"]

        # Size
        if "size" not in ip_module:
            ip_module["size"] = "0x%x" % max(ip["gensize"], 0x1000)
        elif int(ip_module["size"], 0) < ip["gensize"]:
            log.error(
                "given 'size' field in IP %s is smaller than the required space"
                % mod_name)

        # bus_device
        ip_module["bus_device"] = ip["bus_device"]

        # bus_host
        if "bus_host" in ip and ip["bus_host"] != "":
            ip_module["bus_host"] = ip["bus_host"]
        else:
            ip_module["bus_host"] = "none"

        # available_input_list , available_output_list, available_inout_list
        if "available_input_list" in ip:
            ip_module["available_input_list"] = deepcopy(
                ip["available_input_list"])
            for i in ip_module["available_input_list"]:
                i.pop('desc', None)
                i["type"] = "input"
                i["width"] = int(i["width"])
        else:
            ip_module["available_input_list"] = []
        if "available_output_list" in ip:
            ip_module["available_output_list"] = deepcopy(
                ip["available_output_list"])
            for i in ip_module["available_output_list"]:
                i.pop('desc', None)
                i["type"] = "output"
                i["width"] = int(i["width"])
        else:
            ip_module["available_output_list"] = []
        if "available_inout_list" in ip:
            ip_module["available_inout_list"] = deepcopy(
                ip["available_inout_list"])
            for i in ip_module["available_inout_list"]:
                i.pop('desc', None)
                i["type"] = "inout"
                i["width"] = int(i["width"])
        else:
            ip_module["available_inout_list"] = []

        # param_list
        if "param_list" in ip:
            ip_module["param_list"] = deepcopy(ip["param_list"])
            # Removing local parameters.
            for i in ip["param_list"]:
                if i["local"] == "true":
                    ip_module["param_list"].remove(i)
            # Checking for security-relevant parameters
            # that are not exposed, adding a top-level name.
            for i in ip_module["param_list"]:
                par_name = i["name"]
                if par_name.lower().startswith("sec") and not i["expose"]:
                    log.warning("{} has security-critical parameter {} "
                                "not exposed to top".format(
                                    mod_name, par_name))
                # Move special prefixes to the beginnining of the parameter name.
                param_prefixes = ["Sec", "RndCnst"]
                cc_mod_name = c.Name.from_snake_case(mod_name).as_camel_case()
                for prefix in param_prefixes:
                    if par_name.lower().startswith(prefix.lower()):
                        i["name_top"] = prefix + cc_mod_name + par_name[
                            len(prefix):]
                        break
                else:
                    i["name_top"] = cc_mod_name + par_name

                # Generate random bits or permutation, if needed
                if i["randtype"] == "data":
                    i["default"] = _get_random_data_hex_literal(i["randcount"])
                    # Effective width of the random vector
                    i["randwidth"] = int(i["randcount"])
                elif i["randtype"] == "perm":
                    i["default"] = _get_random_perm_hex_literal(i["randcount"])
                    # Effective width of the random vector
                    i["randwidth"] = int(i["randcount"]) * int(
                        ceil(log2(float(i["randcount"]))))
        else:
            ip_module["param_list"] = []

        # interrupt_list
        if "interrupt_list" in ip:
            ip_module["interrupt_list"] = deepcopy(ip["interrupt_list"])
            for i in ip_module["interrupt_list"]:
                i.pop('desc', None)
                i["type"] = "interrupt"
                i["width"] = int(i["width"])
        else:
            ip_module["interrupt_list"] = []

        # alert_list
        if "alert_list" in ip:
            ip_module["alert_list"] = deepcopy(ip["alert_list"])
            for i in ip_module["alert_list"]:
                i.pop('desc', None)
                i["type"] = "alert"
                i["width"] = int(i["width"])
                # automatically insert asynchronous transition if necessary
                if ip_module["clock_srcs"]["clk_i"] == \
                   top["module"][ah_idx]["clock_srcs"]["clk_i"]:
                    i["async"] = 0
                else:
                    i["async"] = 1
        else:
            ip_module["alert_list"] = []

        # wkup_list
        if "wakeup_list" in ip:
            ip_module["wakeup_list"] = deepcopy(ip["wakeup_list"])
            for i in ip_module["wakeup_list"]:
                i.pop('desc', None)
        else:
            ip_module["wakeup_list"] = []

        # reset request
        if "reset_request_list" in ip:
            ip_module["reset_request_list"] = deepcopy(
                ip["reset_request_list"])
            for i in ip_module["reset_request_list"]:
                i.pop('desc', None)
        else:
            ip_module["reset_request_list"] = []

        # scan
        if "scan" in ip:
            ip_module["scan"] = ip["scan"]
        else:
            ip_module["scan"] = "false"

        # scan_reset
        if "scan_reset" in ip:
            ip_module["scan_reset"] = ip["scan_reset"]
        else:
            ip_module["scan_reset"] = "false"

        # inter-module
        if "inter_signal_list" in ip:
            ip_module["inter_signal_list"] = deepcopy(ip["inter_signal_list"])

            # TODO: validate


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
        obj = OrderedDict([
            ("name", host),
            ("clock", xbar['clock']),
            ("reset", xbar['reset']),
            ("type", "host"),
            ("inst_type", ""),
            ("stub", False),
            # The default matches RTL default
            # pipeline_byp is don't care if pipeline is false
            ("pipeline", "true"),
            ("pipeline_byp", "true")
        ])
        xbar["nodes"].append(obj)
        return

    xbar_bool, xbar_h = is_xbar(top, host)
    if xbar_bool:
        log.info("host {} is a crossbar. Nothing to deal with.".format(host))

    obj[0]["xbar"] = xbar_bool

    if 'clock' not in obj[0]:
        obj[0]["clock"] = xbar['clock']

    if 'reset' not in obj[0]:
        obj[0]["reset"] = xbar["reset"]

    obj[0]["stub"] = False
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
    - stub: There is no backing module / memory, instead a tlul port
            is created and forwarded above the current hierarchy
    """
    deviceobj = list(
        filter(lambda node: node["name"] == device,
               top["module"] + top["memory"]))
    nodeobj = list(filter(lambda node: node["name"] == device, xbar["nodes"]))

    xbar_list = [x["name"] for x in top["xbar"] if x["name"] != xbar["name"]]

    # case 1: another xbar --> check in xbar list
    log.info("Handling xbar device {}, devlen {}, nodelen {}".format(
        device, len(deviceobj), len(nodeobj)))
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
            nodeobj[0]["stub"] = False
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
                        "addr_range": [OrderedDict([
                            ("base_addr", top["debug_mem_base_addr"]),
                            ("size_byte", "0x1000"),
                        ])],
                        "xbar": False,
                        "stub": False,
                        "pipeline": "true",
                        "pipeline_byp": "true"
                    })  # yapf: disable
                else:
                    # Update if exists
                    node = nodeobj[0]
                    node["inst_type"] = predefined_modules["debug_mem"]
                    node["addr_range"] = [
                        OrderedDict([("base_addr", top["debug_mem_base_addr"]),
                                     ("size_byte", "0x1000")])
                    ]
                    node["xbar"] = False
                    node["stub"] = False
                    process_pipeline_var(node)
            else:
                log.error("device %s shouldn't be host type" % device)
                return
        # case 3: not defined
        else:
            # Crossbar check
            if len(nodeobj) == 0:
                log.error("""
                    Device %s doesn't exist in 'module', 'memory', predefined,
                    or as a node object
                    """ % device)
            else:
                node = nodeobj[0]
                node["xbar"] = False
                required_keys = ["addr_range"]
                if "stub" in node and node["stub"]:
                    log.info("""
                        Device %s definition is a stub and does not exist in
                        'module', 'memory' or predefined
                        """ % device)

                    if all(key in required_keys for key in node.keys()):
                        log.error(
                            "{}, The xbar only node is missing fields, see {}".
                            format(node['name'], required_keys))
                    process_pipeline_var(node)
                else:
                    log.error("Device {} definition is not a stub!")

            return

    # Search object from module or memory
    elif len(nodeobj) == 0:
        # found in module or memory but node object doesn't exist.
        xbar["nodes"].append({
            "name": device,
            "type": "device",
            "clock": deviceobj[0]["clock"],
            "reset": deviceobj[0]["reset"],
            "inst_type": deviceobj[0]["type"],
            "addr_range": [OrderedDict([
                ("base_addr", deviceobj[0]["base_addr"]),
                ("size_byte", deviceobj[0]["size"])])],
            "pipeline": "true",
            "pipeline_byp": "true",
            "xbar": True if device in xbar_list else False,
            "stub": False
        })  # yapf: disable

    else:
        # found and exist in the nodes too
        node = nodeobj[0]
        node["inst_type"] = deviceobj[0]["type"]
        node["addr_range"] = [
            OrderedDict([("base_addr", deviceobj[0]["base_addr"]),
                         ("size_byte", deviceobj[0]["size"])])
        ]
        node["xbar"] = True if device in xbar_list else False
        node["stub"] = False
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
            if x["type"] == "device" and "xbar" in x and x["xbar"] is False
    ]:
        addr.extend(node["addr_range"])

    # Step 2: visit xbar device ports
    xbar_nodes = [
        x for x in xbar["nodes"]
        if x["type"] == "device" and "xbar" in x and x["xbar"] is True
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
        if "xbar" in node and node["xbar"] is True:
            if "addr_range" not in node:
                # Deeper dive into another crossbar
                xbar_addr = xbar_cross_node(node["name"], host_xbar, xbars,
                                            visited)
                node["addr_range"] = xbar_addr

        result.extend(deepcopy(node["addr_range"]))

    visited.pop()

    return result


# Check if the export field already exists
# If yes, return it
# If no, set a default and return that
def check_clk_rst_export(module):
    if 'clock_reset_export' not in module:
        module['clock_reset_export'] = []
    return module['clock_reset_export']


def amend_clocks(top: OrderedDict):
    """Add a list of clocks to each clock group
       Amend the clock connections of each entry to reflect the actual gated clock
    """
    clks_attr = top['clocks']
    clk_paths = clks_attr['hier_paths']
    groups_in_top = [x["name"].lower() for x in clks_attr['groups']]
    exported_clks = OrderedDict()
    trans_eps = []

    # Assign default parameters to source clocks
    for src in clks_attr['srcs']:
        if 'derived' not in src:
            src['derived'] = "no"
            src['params'] = OrderedDict()

    # Default assignments
    for group in clks_attr['groups']:

        # if unique not defined, it defaults to 'no'
        if 'unique' not in group:
            group['unique'] = "no"

        # if no hardwired clocks, define an empty set
        group['clocks'] = OrderedDict(
        ) if 'clocks' not in group else group['clocks']

    for ep in top['module'] + top['memory'] + top['xbar']:

        clock_connections = OrderedDict()

        # Ensure each module has a default case
        export_if = check_clk_rst_export(ep)

        # if no clock group assigned, default is unique
        ep['clock_group'] = 'secure' if 'clock_group' not in ep else ep[
            'clock_group']
        ep_grp = ep['clock_group']

        # if ep is in the transactional group, collect into list below
        if ep['clock_group'] == 'trans':
            trans_eps.append(ep['name'])

        # end point names and clocks
        ep_name = ep['name']
        ep_clks = []

        # clock group index
        cg_idx = groups_in_top.index(ep_grp)

        # unique property of each group
        unique = clks_attr['groups'][cg_idx]['unique']

        # src property of each group
        src = clks_attr['groups'][cg_idx]['src']

        for port, clk in ep['clock_srcs'].items():
            ep_clks.append(clk)

            name = ''
            hier_name = clk_paths[src]

            if src == 'ext':
                # clock comes from top ports
                if clk == 'main':
                    name = "i"
                else:
                    name = "{}_i".format(clk)

            elif unique == "yes":
                # new unqiue clock name
                name = "{}_{}".format(clk, ep_name)

            else:
                # new group clock name
                name = "{}_{}".format(clk, ep_grp)

            clk_name = "clk_" + name

            # add clock to a particular group
            clks_attr['groups'][cg_idx]['clocks'][clk_name] = clk

            # add clock connections
            clock_connections[port] = hier_name + clk_name

            # clocks for this module are exported
            for intf in export_if:
                log.info("{} export clock name is {}".format(ep_name, name))

                # create dict entry if it does not exit
                if intf not in exported_clks:
                    exported_clks[intf] = OrderedDict()

                # if first time encounter end point, declare
                if ep_name not in exported_clks[intf]:
                    exported_clks[intf][ep_name] = []

                # append clocks
                exported_clks[intf][ep_name].append(name)

        # Add to endpoint structure
        ep['clock_connections'] = clock_connections

    # add entry to top level json
    top['exported_clks'] = exported_clks

    # add entry to inter_module automatically
    for intf in top['exported_clks']:
        top['inter_module']['external']['clkmgr.clocks_{}'.format(
            intf)] = "clks_{}".format(intf)

    # add to intermodule connections
    for ep in trans_eps:
        entry = ep + ".idle"
        top['inter_module']['connect']['clkmgr.idle'].append(entry)


def amend_resets(top):
    """Generate exported reset structure and automatically connect to
       intermodule.
    """
    # Generate exported reset list
    exported_rsts = OrderedDict()
    for module in top["module"]:

        # This code is here to ensure if amend_clocks/resets switched order
        # everything would still work
        export_if = check_clk_rst_export(module)

        # There may be multiple export interfaces
        for intf in export_if:
            # create dict entry if it does not exit
            if intf not in exported_rsts:
                exported_rsts[intf] = OrderedDict()

            # grab directly from reset_connections definition
            rsts = [rst for rst in module['reset_connections'].values()]
            exported_rsts[intf][module['name']] = rsts

    # add entry to top level json
    top['exported_rsts'] = exported_rsts

    # add entry to inter_module automatically
    for intf in top['exported_rsts']:
        top['inter_module']['external']['rstmgr.resets_{}'.format(
            intf)] = "rsts_{}".format(intf)
    """Discover the full path and selection to each reset connection.
       This is done by modifying the reset connection of each end point.
    """
    for end_point in top['module'] + top['memory'] + top['xbar']:
        for port, net in end_point['reset_connections'].items():
            reset_path = lib.get_reset_path(net, end_point['domain'],
                                            top['resets'])
            end_point['reset_connections'][port] = reset_path

    # reset paths are still needed temporarily until host only modules are properly automated
    reset_paths = OrderedDict()
    reset_hiers = top["resets"]['hier_paths']

    for reset in top["resets"]["nodes"]:
        if "type" not in reset:
            log.error("{} missing type field".format(reset["name"]))
            return

        if reset["type"] == "top":
            reset_paths[reset["name"]] = "{}rst_{}_n".format(
                reset_hiers["top"], reset["name"])

        elif reset["type"] == "ext":
            reset_paths[reset["name"]] = reset_hiers["ext"] + reset['name']
        elif reset["type"] == "int":
            log.info("{} used as internal reset".format(reset["name"]))
        else:
            log.error("{} type is invalid".format(reset["type"]))

    top["reset_paths"] = reset_paths

    return


def amend_interrupt(top):
    """Check interrupt_module if exists, or just use all modules
    """
    if "interrupt_module" not in top:
        top["interrupt_module"] = [x["name"] for x in top["module"]]

    if "interrupt" not in top or top["interrupt"] == "":
        top["interrupt"] = []

    for m in top["interrupt_module"]:
        ip = list(filter(lambda module: module["name"] == m, top["module"]))
        if len(ip) == 0:
            log.warning(
                "Cannot find IP %s which is used in the interrupt_module" % m)
            continue

        log.info("Adding interrupts from module %s" % ip[0]["name"])
        top["interrupt"] += list(
            map(partial(lib.add_module_prefix_to_signal, module=m.lower()),
                ip[0]["interrupt_list"]))


def amend_alert(top):
    """Check interrupt_module if exists, or just use all modules
    """
    if "alert_module" not in top:
        top["alert_module"] = [x["name"] for x in top["module"]]

    if "alert" not in top or top["alert"] == "":
        top["alert"] = []

    for m in top["alert_module"]:
        ip = list(filter(lambda module: module["name"] == m, top["module"]))
        if len(ip) == 0:
            log.warning("Cannot find IP %s which is used in the alert_module" %
                        m)
            continue

        log.info("Adding alert from module %s" % ip[0]["name"])
        top["alert"] += list(
            map(partial(lib.add_module_prefix_to_signal, module=m.lower()),
                ip[0]["alert_list"]))


def amend_wkup(topcfg: OrderedDict):

    if "wakeups" not in topcfg or topcfg["wakeups"] == "":
        topcfg["wakeups"] = []

    # create list of wakeup signals
    for m in topcfg["module"]:
        log.info("Adding wakeup from module %s" % m["name"])
        for entry in m["wakeup_list"]:
            log.info("Adding singal %s" % entry["name"])
            signal = deepcopy(entry)
            signal["module"] = m["name"]
            topcfg["wakeups"].append(signal)

    # add wakeup signals to pwrmgr connections
    signal_names = [
        "{}.{}".format(s["module"].lower(), s["name"].lower())
        for s in topcfg["wakeups"]
    ]
    # TBD: What's the best way to not hardcode this signal below?
    #      We could make this a top.hjson variable and validate it against pwrmgr hjson
    topcfg["inter_module"]["connect"]["pwrmgr.wakeups"] = signal_names
    log.info("Intermodule signals: {}".format(
        topcfg["inter_module"]["connect"]))


# Handle reset requests from modules
def amend_reset_request(topcfg: OrderedDict):

    if "reset_requests" not in topcfg or topcfg["reset_requests"] == "":
        topcfg["reset_requests"] = []

    # create list of reset signals
    for m in topcfg["module"]:
        log.info("Adding reset requests from module %s" % m["name"])
        for entry in m["reset_request_list"]:
            log.info("Adding singal %s" % entry["name"])
            signal = deepcopy(entry)
            signal["module"] = m["name"]
            topcfg["reset_requests"].append(signal)

    # add reset requests to pwrmgr connections
    signal_names = [
        "{}.{}".format(s["module"].lower(), s["name"].lower())
        for s in topcfg["reset_requests"]
    ]
    # TBD: What's the best way to not hardcode this signal below?
    #      We could make this a top.hjson variable and validate it against pwrmgr hjson
    topcfg["inter_module"]["connect"]["pwrmgr.rstreqs"] = signal_names
    log.info("Intermodule signals: {}".format(
        topcfg["inter_module"]["connect"]))


def amend_pinmux_io(top):
    """ Check dio_modules/ mio_modules. If not exists, add all modules to mio
    """
    pinmux = top["pinmux"]

    if "dio_modules" not in pinmux:
        pinmux['dio_modules'] = []

    # list out dedicated IO
    pinmux['dio'] = []
    for e in pinmux["dio_modules"]:
        # Check name if it is module or signal
        mname, sname = lib.get_ms_name(e["name"])

        # Parse how many signals
        m = lib.get_module_by_name(top, mname)

        if m is None:
            raise SystemExit("Module {} in `dio_modules`"
                             " is not searchable.".format(mname))

        if sname is not None:
            signals = deepcopy([lib.get_signal_by_name(m, sname)])
        else:
            # Get all module signals
            signals = deepcopy(m["available_input_list"] +
                               m["available_output_list"] +
                               m["available_inout_list"])

        sig_width = sum([s["width"] for s in signals])

        # convert signal with module name
        signals = list(
            map(partial(lib.add_module_prefix_to_signal, module=mname),
                signals))
        # Parse how many pads are assigned
        if "pad" not in e:
            raise SystemExit("Should catch pad field in validate.py!")

        # pads are the list of individual pin, each entry is 1 bit width
        pads = []
        for p in e["pad"]:
            pads += lib.get_pad_list(p)

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

    # Multiplexer IO
    if "mio_modules" not in pinmux:
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
    if "inputs" not in pinmux:
        pinmux["inputs"] = []
    if "outputs" not in pinmux:
        pinmux["outputs"] = []
    if "inouts" not in pinmux:
        pinmux["inouts"] = []

    for e in pinmux["mio_modules"]:
        tokens = e.split('.')
        if len(tokens) not in [1, 2]:
            raise SystemExit(
                "Cannot parse signal/module in mio_modules {}".format(e))
        # Add all ports from the module to input/outputs
        m = lib.get_module_by_name(top, tokens[0])
        if m is None:
            raise SystemExit("Module {} doesn't exist".format(tokens[0]))

        if len(tokens) == 1:
            pinmux["inputs"] += list(
                filter(
                    lambda x: x["name"] not in dio_names,
                    map(
                        partial(lib.add_module_prefix_to_signal,
                                module=m["name"].lower()),
                        m["available_input_list"])))
            pinmux["outputs"] += list(
                filter(
                    lambda x: x["name"] not in dio_names,
                    map(
                        partial(lib.add_module_prefix_to_signal,
                                module=m["name"].lower()),
                        m["available_output_list"])))
            pinmux["inouts"] += list(
                filter(
                    lambda x: x["name"] not in dio_names,
                    map(
                        partial(lib.add_module_prefix_to_signal,
                                module=m["name"].lower()),
                        m["available_inout_list"])))

        elif len(tokens) == 2:
            # Current version doesn't consider signal in mio_modules
            # only in dio_modules
            raise SystemExit(
                "Curren version doesn't support signal in mio_modules {}".
                format(e))


def merge_top(topcfg: OrderedDict, ipobjs: OrderedDict,
              xbarobjs: OrderedDict) -> OrderedDict:
    gencfg = topcfg

    # Combine ip cfg into topcfg
    for ip in ipobjs:
        amend_ip(gencfg, ip)

    # Create clock connections for each block
    # Assign clocks into appropriate groups
    # Note, amend_ip references clock information to establish async handling
    # as part of alerts.
    # amend_clocks(gencfg)

    # Combine the wakeups
    amend_wkup(gencfg)
    amend_reset_request(gencfg)

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

    # Add path names to declared resets.
    # Declare structure for exported resets.
    amend_resets(gencfg)

    # remove unwanted fields 'debug_mem_base_addr'
    gencfg.pop('debug_mem_base_addr', None)

    return gencfg
