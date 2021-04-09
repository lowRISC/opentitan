# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import random
from collections import OrderedDict
from copy import deepcopy
from math import ceil, log2
from typing import Dict, List

from topgen import c, lib
from reggen.ip_block import IpBlock
from reggen.params import LocalParam, Parameter, RandParameter


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


def elaborate_instances(top, name_to_block: Dict[str, IpBlock]):
    '''Add additional fields to the elements of top['module']

    These elements represent instantiations of IP blocks. This function adds
    extra fields to them to carry across information from the IpBlock objects
    that represent the blocks being instantiated. See elaborate_instance for
    more details of what gets added.

    '''
    # Initialize RNG for compile-time netlist constants.
    random.seed(int(top['rnd_cnst_seed']))

    for instance in top['module']:
        block = name_to_block[instance['type']]
        elaborate_instance(instance, block)


def elaborate_instance(instance, block: IpBlock):
    """Add additional fields to a single instance of a module.

    instance is the instance to be filled in. block is the block that it's
    instantiating.

    Altered fields:
        - param_list (list of parameters for the instance)
        - inter_signal_list (list of inter-module signals)
        - base_addrs (a map from interface name to its base address)

    Removed fields:
        - base_addr (this is reflected in base_addrs)

    """
    mod_name = instance["name"]

    # param_list
    new_params = []
    for param in block.params.by_name.values():
        if isinstance(param, LocalParam):
            # Remove local parameters.
            continue

        new_param = param.as_dict()

        param_expose = param.expose if isinstance(param, Parameter) else False

        # Check for security-relevant parameters that are not exposed,
        # adding a top-level name.
        if param.name.lower().startswith("sec") and not param_expose:
            log.warning("{} has security-critical parameter {} "
                        "not exposed to top".format(
                            mod_name, param.name))

        # Move special prefixes to the beginnining of the parameter name.
        param_prefixes = ["Sec", "RndCnst"]
        cc_mod_name = c.Name.from_snake_case(mod_name).as_camel_case()
        name_top = cc_mod_name + param.name
        for prefix in param_prefixes:
            if param.name.lower().startswith(prefix.lower()):
                name_top = (prefix + cc_mod_name +
                            param.name[len(prefix):])
                break

        new_param['name_top'] = name_top

        # Generate random bits or permutation, if needed
        if isinstance(param, RandParameter):
            if param.randtype == 'data':
                new_default = _get_random_data_hex_literal(param.randcount)
                # Effective width of the random vector
                randwidth = param.randcount
            else:
                assert param.randtype == 'perm'
                new_default = _get_random_perm_hex_literal(param.randcount)
                # Effective width of the random vector
                randwidth = param.randcount * ceil(log2(param.randcount))

            new_param['default'] = new_default
            new_param['randwidth'] = randwidth

        new_params.append(new_param)

    instance["param_list"] = new_params

    # These objects get added-to in place by code in intermodule.py, so we have
    # to convert and copy them here.
    instance["inter_signal_list"] = [s.as_dict() for s in block.inter_signals]

    # An instance must either have a 'base_addr' address or a 'base_addrs'
    # address, but can't have both.
    base_addrs = instance.get('base_addrs')
    if base_addrs is None:
        if 'base_addr' not in instance:
            log.error('Instance {!r} has neither a base_addr '
                      'nor a base_addrs field.'
                      .format(instance['name']))
        else:
            # If the instance has a base_addr field, make sure that the block
            # has just one device interface.
            if len(block.reg_blocks) != 1:
                log.error('Instance {!r} has a base_addr field but it '
                          'instantiates the block {!r}, which has {} '
                          'device interfaces.'
                          .format(instance['name'],
                                  block.name, len(block.reg_blocks)))
            else:
                if_name = next(iter(block.reg_blocks))
                base_addrs = {if_name: instance['base_addr']}

        # Fill in a bogus base address (we don't have proper error handling, so
        # have to do *something*)
        if base_addrs is None:
            base_addrs = {None: 0}

        instance['base_addrs'] = base_addrs
    else:
        if 'base_addr' in instance:
            log.error('Instance {!r} has both a base_addr '
                      'and a base_addrs field.'
                      .format(instance['name']))

        # Since the instance already has a base_addrs field, make sure that
        # it's got the same set of keys as the name of the interfaces in the
        # block.
        inst_if_names = set(base_addrs.keys())
        block_if_names = set(block.reg_blocks.keys())
        if block_if_names != inst_if_names:
            log.error('Instance {!r} has a base_addrs field with keys {} '
                      'but the block it instantiates ({!r}) has device '
                      'interfaces {}.'
                      .format(instance['name'], inst_if_names,
                              block.name, block_if_names))

    if 'base_addr' in instance:
        del instance['base_addr']


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


def xbar_adddevice(top: Dict[str, object],
                   name_to_block: Dict[str, IpBlock],
                   xbar: Dict[str, object],
                   other_xbars: List[str],
                   device: str) -> None:
    """Add or amend an entry in xbar['nodes'] to represent the device interface

    - clock: comes from module if exist, use xbar default otherwise
    - reset: comes from module if exist, use xbar default otherwise
    - inst_type: comes from module or memory if exist.
    - base_addr: comes from module or memory, or assume rv_plic?
    - size_byte: comes from module or memory
    - xbar: bool, true if the device port is another xbar
    - stub: There is no backing module / memory, instead a tlul port
            is created and forwarded above the current hierarchy
    """
    device_parts = device.split('.', 1)
    device_base = device_parts[0]
    device_ifname = device_parts[1] if len(device_parts) > 1 else None

    # Try to find a block or memory instance with name device_base. Object
    # names should be unique, so there should never be more than one hit.
    instances = [
        node for node in top["module"] + top["memory"]
        if node['name'] == device_base
    ]
    assert len(instances) <= 1
    inst = instances[0] if instances else None

    # Try to find a node in the crossbar called device. Node names should be
    # unique, so there should never be more than one hit.
    nodes = [
        node for node in xbar['nodes']
        if node['name'] == device
    ]
    assert len(nodes) <= 1
    node = nodes[0] if nodes else None

    log.info("Handling xbar device {} (matches instance? {}; matches node? {})"
             .format(device, inst is not None, node is not None))

    # case 1: another xbar --> check in xbar list
    if node is None and device in other_xbars:
        log.error(
            "Another crossbar %s needs to be specified in the 'nodes' list" %
            device)
        return

    # If there is no module or memory with the right name, this might still be
    # ok: we might be connecting to another crossbar or to a predefined module.
    if inst is None:
        # case 1: Crossbar handling
        if device in other_xbars:
            log.info(
                "device {} in Xbar {} is connected to another Xbar".format(
                    device, xbar["name"]))
            assert node is not None
            node["xbar"] = True
            node["stub"] = False
            process_pipeline_var(node)
            return

        # case 2: predefined_modules (debug_mem, rv_plic)
        # TODO: Find configurable solution not from predefined but from object?
        if device in predefined_modules:
            if device == "debug_mem":
                if node is None:
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
        # Crossbar check
        log.error("Device %s doesn't exist in 'module', 'memory', predefined, "
                  "or as a node object" % device)
        return

    # If we get here, inst points an instance of some block or memory. It
    # shouldn't point at a crossbar (because that would imply a naming clash)
    assert device_base not in other_xbars
    base_addr, size_byte = lib.get_base_and_size(name_to_block,
                                                 inst, device_ifname)
    addr_range = {"base_addr": hex(base_addr), "size_byte": hex(size_byte)}

    stub = not lib.is_inst(inst)

    if node is None:
        log.error('Cannot connect to {!r} because '
                  'the crossbar defines no node for {!r}.'
                  .format(device, device_base))
        return

    node["inst_type"] = inst["type"]
    node["addr_range"] = [addr_range]
    node["xbar"] = False
    node["stub"] = stub
    process_pipeline_var(node)


def amend_xbar(top: Dict[str, object],
               name_to_block: Dict[str, IpBlock],
               xbar: Dict[str, object]):
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

    other_xbars = [x["name"]
                   for x in top["xbar"]
                   if x["name"] != xbar["name"]]

    log.info(device_nodes)
    for device in device_nodes:
        xbar_adddevice(top, name_to_block, topxbar, other_xbars, device)


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


# find the first instance name of a given type
def _find_module_name(modules, module_type):
    for m in modules:
        if m['type'] == module_type:
            return m['name']

    return None


def amend_clocks(top: OrderedDict):
    """Add a list of clocks to each clock group
       Amend the clock connections of each entry to reflect the actual gated clock
    """
    clks_attr = top['clocks']
    clk_paths = clks_attr['hier_paths']
    clkmgr_name = _find_module_name(top['module'], 'clkmgr')
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
        export_if = ep.get('clock_reset_export', [])

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
        top['inter_module']['external']['{}.clocks_{}'.format(
            clkmgr_name, intf)] = "clks_{}".format(intf)

    # add to intermodule connections
    for ep in trans_eps:
        entry = ep + ".idle"
        top['inter_module']['connect']['{}.idle'.format(clkmgr_name)].append(entry)


def amend_resets(top):
    """Generate exported reset structure and automatically connect to
       intermodule.
    """

    rstmgr_name = _find_module_name(top['module'], 'rstmgr')

    # Generate exported reset list
    exported_rsts = OrderedDict()
    for module in top["module"]:

        # This code is here to ensure if amend_clocks/resets switched order
        # everything would still work
        export_if = module.get('clock_reset_export', [])

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
        top['inter_module']['external']['{}.resets_{}'.format(
            rstmgr_name, intf)] = "rsts_{}".format(intf)
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


def ensure_interrupt_modules(top: OrderedDict, name_to_block: Dict[str, IpBlock]):
    '''Populate top['interrupt_module'] if necessary

    Do this by adding each module in top['modules'] that defines at least one
    interrupt.

    '''
    if 'interrupt_module' in top:
        return

    modules = []
    for module in top['module']:
        block = name_to_block[module['type']]
        if block.interrupts:
            modules.append(module['name'])

    top['interrupt_module'] = modules


def amend_interrupt(top: OrderedDict, name_to_block: Dict[str, IpBlock]):
    """Check interrupt_module if exists, or just use all modules
    """
    ensure_interrupt_modules(top, name_to_block)

    if "interrupt" not in top or top["interrupt"] == "":
        top["interrupt"] = []

    for m in top["interrupt_module"]:
        ips = list(filter(lambda module: module["name"] == m, top["module"]))
        if len(ips) == 0:
            log.warning(
                "Cannot find IP %s which is used in the interrupt_module" % m)
            continue

        ip = ips[0]
        block = name_to_block[ip['type']]

        log.info("Adding interrupts from module %s" % ip["name"])
        for signal in block.interrupts:
            sig_dict = signal.as_nwt_dict('interrupt')
            qual = lib.add_module_prefix_to_signal(sig_dict,
                                                   module=m.lower())
            top["interrupt"].append(qual)


def ensure_alert_modules(top: OrderedDict, name_to_block: Dict[str, IpBlock]):
    '''Populate top['alert_module'] if necessary

    Do this by adding each module in top['modules'] that defines at least one
    alert.

    '''
    if 'alert_module' in top:
        return

    modules = []
    for module in top['module']:
        block = name_to_block[module['type']]
        if block.alerts:
            modules.append(module['name'])

    top['alert_module'] = modules


def amend_alert(top: OrderedDict, name_to_block: Dict[str, IpBlock]):
    """Check interrupt_module if exists, or just use all modules
    """
    ensure_alert_modules(top, name_to_block)

    if "alert" not in top or top["alert"] == "":
        top["alert"] = []

    # Find the alert handler and extract the name of its clock
    alert_clock = None
    for instance in top['module']:
        if instance['type'].lower() == 'alert_handler':
            alert_clock = instance['clock_srcs']['clk_i']
            break
    assert alert_clock is not None

    for m in top["alert_module"]:
        ips = list(filter(lambda module: module["name"] == m, top["module"]))
        if len(ips) == 0:
            log.warning("Cannot find IP %s which is used in the alert_module" %
                        m)
            continue

        ip = ips[0]
        block = name_to_block[ip['type']]

        log.info("Adding alert from module %s" % ip["name"])
        has_async_alerts = ip['clock_srcs']['clk_i'] != alert_clock
        for alert in block.alerts:
            alert_dict = alert.as_nwt_dict('alert')
            alert_dict['async'] = '1' if has_async_alerts else '0'
            qual_sig = lib.add_module_prefix_to_signal(alert_dict,
                                                       module=m.lower())
            top["alert"].append(qual_sig)


def amend_wkup(topcfg: OrderedDict, name_to_block: Dict[str, IpBlock]):

    pwrmgr_name = _find_module_name(topcfg['module'], 'pwrmgr')

    if "wakeups" not in topcfg or topcfg["wakeups"] == "":
        topcfg["wakeups"] = []

    # create list of wakeup signals
    for m in topcfg["module"]:
        log.info("Adding wakeup from module %s" % m["name"])
        block = name_to_block[m['type']]
        for signal in block.wakeups:
            log.info("Adding signal %s" % signal.name)
            topcfg["wakeups"].append({
                'name': signal.name,
                'width': str(signal.bits.width()),
                'module': m["name"]
            })

    # add wakeup signals to pwrmgr connections
    signal_names = [
        "{}.{}".format(s["module"].lower(), s["name"].lower())
        for s in topcfg["wakeups"]
    ]

    topcfg["inter_module"]["connect"]["{}.wakeups".format(pwrmgr_name)] = signal_names
    log.info("Intermodule signals: {}".format(
        topcfg["inter_module"]["connect"]))


# Handle reset requests from modules
def amend_reset_request(topcfg: OrderedDict,
                        name_to_block: Dict[str, IpBlock]):

    pwrmgr_name = _find_module_name(topcfg['module'], 'pwrmgr')

    if "reset_requests" not in topcfg or topcfg["reset_requests"] == "":
        topcfg["reset_requests"] = []

    # create list of reset signals
    for m in topcfg["module"]:
        log.info("Adding reset requests from module %s" % m["name"])
        block = name_to_block[m['type']]
        for signal in block.reset_requests:
            log.info("Adding signal %s" % signal.name)
            topcfg["reset_requests"].append({
                'name': signal.name,
                'width': str(signal.bits.width()),
                'module': m["name"]
            })

    # add reset requests to pwrmgr connections
    signal_names = [
        "{}.{}".format(s["module"].lower(), s["name"].lower())
        for s in topcfg["reset_requests"]
    ]

    topcfg["inter_module"]["connect"]["{}.rstreqs".format(pwrmgr_name)] = signal_names
    log.info("Intermodule signals: {}".format(
        topcfg["inter_module"]["connect"]))


def append_io_signal(temp: Dict, sig_inst: Dict) -> None:
    '''Appends the signal to the correct list'''
    if sig_inst['type'] == 'inout':
        temp['inouts'].append(sig_inst)
    if sig_inst['type'] == 'input':
        temp['inputs'].append(sig_inst)
    if sig_inst['type'] == 'output':
        temp['outputs'].append(sig_inst)


def get_index_and_incr(ctrs: Dict, connection: str, io_dir: str) -> Dict:
    '''Get correct index counter and increment'''

    if connection != 'muxed':
        connection = 'dedicated'

    if io_dir in 'inout':
        result = ctrs[connection]['inouts']
        ctrs[connection]['inouts'] += 1
    elif connection == 'muxed':
        # For MIOs, the input/output arrays differ in RTL
        # I.e., the input array contains {inputs, inouts}, whereas
        # the output array contains {outputs, inouts}.
        if io_dir == 'input':
            result = ctrs[connection]['inputs'] + ctrs[connection]['inouts']
            ctrs[connection]['inputs'] += 1
        elif io_dir == 'output':
            result = ctrs[connection]['outputs'] + ctrs[connection]['inouts']
            ctrs[connection]['outputs'] += 1
        else:
            assert(0)  # should not happen
    else:
        # For DIOs, the input/output arrays are identical in terms of index layout.
        # Unused inputs are left unconnected and unused outputs are tied off.
        if io_dir == 'input':
            result = ctrs[connection]['inputs'] + ctrs[connection]['inouts']
            ctrs[connection]['inputs'] += 1
        elif io_dir == 'output':
            result = (ctrs[connection]['outputs'] +
                      ctrs[connection]['inouts'] +
                      ctrs[connection]['inputs'])
            ctrs[connection]['outputs'] += 1
        else:
            assert(0)  # should not happen

    return result


def amend_pinmux_io(top: Dict, name_to_block: Dict[str, IpBlock]):
    """ Process pinmux/pinout configuration and assign available IOs
    """
    pinmux = top['pinmux']
    pinout = top['pinout']
    targets = top['targets']

    temp = {}
    temp['inouts'] = []
    temp['inputs'] = []
    temp['outputs'] = []

    for sig in pinmux['signals']:
        # Get the signal information from the IP block type of this instance/
        mod_name = sig['instance']
        m = lib.get_module_by_name(top, mod_name)

        if m is None:
            raise SystemExit("Module {} is not searchable.".format(mod_name))

        block = name_to_block[m['type']]

        # If the signal is explicitly named.
        if sig['port'] != '':

            # If this is a bus signal with explicit indexes.
            if '[' in sig['port']:
                name_split = sig['port'].split('[')
                sig_name = name_split[0]
                idx = int(name_split[1][:-1])
            else:
                idx = -1
                sig_name = sig['port']

            sig_inst = deepcopy(block.get_signal_by_name_as_dict(sig_name))

            if idx >= 0 and idx >= sig_inst['width']:
                raise SystemExit("Index {} is out of bounds for signal {}"
                                 " with width {}.".format(idx, sig_name, sig_inst['width']))
            if idx == -1 and sig_inst['width'] != 1:
                raise SystemExit("Bus signal {} requires an index.".format(sig_name))

            # If we got this far we know that the signal is valid and exists.
            # Augment this signal instance with additional information.
            sig_inst.update({'idx': idx,
                             'pad': sig['pad'],
                             'attr': sig['attr'],
                             'connection': sig['connection']})
            sig_inst['name'] = mod_name + '_' + sig_inst['name']
            append_io_signal(temp, sig_inst)

        # Otherwise the name is a wildcard for selecting all available IO signals
        # of this block and we need to extract them here one by one signals here.
        else:
            sig_list = deepcopy(block.get_signals_as_list_of_dicts())

            for sig_inst in sig_list:
                # If this is a multibit signal, unroll the bus and
                # generate a single bit IO signal entry for each one.
                if sig_inst['width'] > 1:
                    for idx in range(sig_inst['width']):
                        sig_inst_copy = deepcopy(sig_inst)
                        sig_inst_copy.update({'idx': idx,
                                              'pad': sig['pad'],
                                              'attr': sig['attr'],
                                              'connection': sig['connection']})
                        sig_inst_copy['name'] = sig['instance'] + '_' + sig_inst_copy['name']
                        append_io_signal(temp, sig_inst_copy)
                else:
                    sig_inst.update({'idx': -1,
                                     'pad': sig['pad'],
                                     'attr': sig['attr'],
                                     'connection': sig['connection']})
                    sig_inst['name'] = sig['instance'] + '_' + sig_inst['name']
                    append_io_signal(temp, sig_inst)

    # Now that we've collected all input and output signals,
    # we can go through once again and stack them into one unified
    # list, and calculate MIO/DIO global indices.
    pinmux['ios'] = (temp['inouts'] +
                     temp['inputs'] +
                     temp['outputs'])

    # Remember these counts to facilitate the RTL generation
    pinmux['io_counts'] = {'dedicated': {'inouts': 0, 'inputs': 0, 'outputs': 0, 'pads': 0},
                           'muxed': {'inouts': 0, 'inputs': 0, 'outputs': 0, 'pads': 0}}

    for sig in pinmux['ios']:
        glob_idx = get_index_and_incr(pinmux['io_counts'], sig['connection'], sig['type'])
        sig['glob_idx'] = glob_idx

    # Calculate global indices for pads.
    j = k = 0
    for pad in pinout['pads']:
        if pad['connection'] == 'muxed':
            pad['idx'] = j
            j += 1
        else:
            pad['idx'] = k
            k += 1
    pinmux['io_counts']['muxed']['pads'] = j
    pinmux['io_counts']['dedicated']['pads'] = k

    # For each target configuration, calculate the special signal indices.
    known_muxed_pads = {}
    for pad in pinout['pads']:
        if pad['connection'] == 'muxed':
            known_muxed_pads[pad['name']] = pad

    known_mapped_dio_pads = {}
    for sig in pinmux['ios']:
        if sig['connection'] in ['muxed', 'manual']:
            continue
        if sig['pad'] in known_mapped_dio_pads:
            raise SystemExit('Cannot have multiple IOs mapped to the same DIO pad {}'
                             .format(sig['pad']))
        known_mapped_dio_pads[sig['pad']] = sig

    for target in targets:
        for entry in target['pinmux']['special_signals']:
            # If this is a muxed pad, the resolution is
            # straightforward. I.e., we just assign the MIO index.
            if entry['pad'] in known_muxed_pads:
                entry['idx'] = known_muxed_pads[entry['pad']]['idx']
            # Otherwise we need to find out which DIO this pad is mapped to.
            # Note that we can't have special_signals that are manual, since
            # there needs to exist a DIO connection.
            elif entry['pad'] in known_mapped_dio_pads:
                # This index refers to the stacked {dio, mio} array
                # on the chip-level, hence we have to add the amount of MIO pads.
                idx = (known_mapped_dio_pads[entry['pad']]['glob_idx'] +
                       pinmux['io_counts']['muxed']['pads'])
                entry['idx'] = idx
            else:
                assert(0)  # Entry should be guaranteed to exist at this point


def merge_top(topcfg: OrderedDict,
              name_to_block: Dict[str, IpBlock],
              xbarobjs: OrderedDict) -> OrderedDict:

    # Combine ip cfg into topcfg
    elaborate_instances(topcfg, name_to_block)

    # Create clock connections for each block
    # Assign clocks into appropriate groups
    # Note, elaborate_instances references clock information to establish async handling
    # as part of alerts.
    # amend_clocks(topcfg)

    # Combine the wakeups
    amend_wkup(topcfg, name_to_block)
    amend_reset_request(topcfg, name_to_block)

    # Combine the interrupt (should be processed prior to xbar)
    amend_interrupt(topcfg, name_to_block)

    # Combine the alert (should be processed prior to xbar)
    amend_alert(topcfg, name_to_block)

    # Creates input/output list in the pinmux
    log.info("Processing PINMUX")
    amend_pinmux_io(topcfg, name_to_block)

    # Combine xbar into topcfg
    for xbar in xbarobjs:
        amend_xbar(topcfg, name_to_block, xbar)

    # 2nd phase of xbar (gathering the devices address range)
    for xbar in topcfg["xbar"]:
        xbar_cross(xbar, topcfg["xbar"])

    # Add path names to declared resets.
    # Declare structure for exported resets.
    amend_resets(topcfg)

    # remove unwanted fields 'debug_mem_base_addr'
    topcfg.pop('debug_mem_base_addr', None)

    return topcfg
