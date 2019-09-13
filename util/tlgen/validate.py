# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import logging as log
from collections import OrderedDict

from .item import Edge, Node, NodeType
from .xbar import Xbar


def get_nodetype(t):  # t: str -> NodeType
    if t == "host":
        return NodeType.HOST
    elif t == "device":
        return NodeType.DEVICE
    elif t == "async_fifo":
        return NodeType.ASYNC_FIFO
    elif t == "socket_1n":
        return NodeType.SOCKET_1N
    elif t == "socket_m1":
        return NodeType.SOCKET_M1

    raise


def checkNameExist(name, xbar):  # name: str -> xbar: Xbar -> bool
    return name.lower() in [x.name for x in xbar.nodes]


def isOverlap(range1, range2):  # Tuple[int,int] -> Tuple[int,int] -> bool
    return not (range2[1] < range1[0] or range2[0] > range1[1])


# Tuple[int,int] -> List[Tuple[]] -> bool
def checkAddressOverlap(addr, ranges):
    result = [x for x in ranges if isOverlap(x, addr)]
    return len(result) != 0


def validate(obj):  # OrderedDict -> Xbar
    xbar = Xbar()
    xbar.name = obj["name"].lower()
    xbar.clock = obj["clock"].lower()

    addr_ranges = []

    # Nodes
    for nodeobj in obj["nodes"]:
        clock = nodeobj["clock"].lower() if "clock" in nodeobj.keys(
        ) else xbar.clock

        if checkNameExist(nodeobj["name"], xbar):
            log.error("Duplicated name: %s" % (nodeobj["name"]))
            raise SystemExit("Duplicated name in the configuration")

        node = Node(name=nodeobj["name"].lower(),
                    node_type=get_nodetype(nodeobj["type"].lower()),
                    clock=clock)

        if node.node_type == NodeType.DEVICE:
            # Add address obj["base_addr"], obj["size"])
            node.address_from = int(nodeobj["base_addr"], 0)
            size = int(nodeobj["size_byte"], 0)
            node.address_to = node.address_from + size - 1

            addr = (node.address_from, node.address_to)

            if checkAddressOverlap(addr, addr_ranges):
                log.error(
                    "Address is overlapping. Check the config. Addr(0x%x - 0x%x)"
                    % (addr[0], addr[1]))
                raise SystemExit("Address overlapping error occurred")

            addr_ranges.append(addr)

        if node.node_type in [NodeType.DEVICE, NodeType.HOST
                              ] and "pipeline" in nodeobj:
            node.pipeline = True if nodeobj["pipeline"].lower() in [
                "true", "1"
            ] else False
            node.pipeline_byp = True if nodeobj["pipeline_byp"].lower() in [
                "true", "1"
            ] else False
        xbar.nodes.append(node)

    # Edge
    for host in obj["connections"].keys():
        # host: [device]
        for device in obj["connections"][host]:
            xbar.connect_nodes(host.lower(), device.lower())

    return xbar
