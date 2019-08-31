# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import copy
import logging as log

from .item import Edge, Node, NodeType
from .xbar import Xbar


def elaborate(xbar):  # xbar: Xbar -> bool
    """elaborate reads all nodes and edges then
    construct internal FIFOs, Sockets.
    """
    # Condition check
    if len(xbar.nodes) <= 1 or len(xbar.edges) == 0:
        log.error(
            "# of Nodes is less than 2 or no Edge exists. Cannot proceed.")
        return False

    for host in xbar.hosts:
        process_node(host, xbar)
        log.info("Node Processed: " + repr(xbar))

    ## Pipeline
    process_pipeline(xbar)

    ## Build address map
    ## Each socket_1n should have address map

    ## Gather clocks
    xbar.clocks = {xbar.clock
                   } | {clk
                        for node in xbar.nodes for clk in node.clocks}

    return True


def process_node(node, xbar):  # node: Node -> xbar: Xbar -> Xbar
    """process each node based on algorithm

    1. If a node has different clock from main clock and not ASYNC_FIFO:
       a. (New Node) Create ASYNC_FIFO node.
       b. Revise every edges from the node to have start node as ASYNC_FIFO
          node. (New Edge) create a edge from the node to ASYNC_FIFO node.
          - Repeat the algorithm with ASYNC_FIFO node.
       c. Revise every edges to the node to have end node as ASYNC_FIFO
          node. (New Edge) create a edge from ASYNC_FIFO node to the node.
       d. If it is not DEVICE, HOST node, raise Error. If it is DEVICE, end
          (next item).
    2. If a node has multiple edges having it as a end node and not SOCKET_M1:
       a. (New node) Create SOCKET_M1 node.
       b. Revise every edges to the node to have SOCKET_M1 node as end node.
       c. (New Edge) create a edge from SOCKET_M1 to the node.
       d. Repeat the algorithm with the node.
    3. If a node has multiple edges having it as a start node and not SOCKET_1N:
       a. (New node) Create SOCKET_1N node.
       b. Revise every edges from the node to have SOCKET_1N node as start node.
       c. (New Edge) Create a edge from the node to SOCKET_1N node.
       d. (for loop) Repeat the algorithm with SOCKET_1N’s other side node.
    """

    # If a node has different clock from main clock and not ASYNC_FIFO:
    if node.node_type != NodeType.ASYNC_FIFO and node.clocks[0] != xbar.clock:
        # (New Node) Create ASYNC_FIFO node
        new_node = Node(name="asf_" + str(len(xbar.nodes)),
                        node_type=NodeType.ASYNC_FIFO,
                        clock=xbar.clock)
        if node.node_type == NodeType.HOST:
            new_node.clocks.insert(0, node.clocks[0])
        else:
            new_node.clocks.append(node.clocks[0])

        xbar.insert_node(new_node, node)

        process_node(new_node, xbar)

    # If a node has multiple edges having it as a end node and not SOCKET_M1:
    elif node.node_type != NodeType.SOCKET_M1 and len(node.us) > 1:
        # (New node) Create SOCKET_M1 node
        new_node = Node(name="sm1_" + str(len(xbar.nodes)),
                        node_type=NodeType.SOCKET_M1,
                        clock=xbar.clock)
        new_node.hpass = 2**len(node.us) - 1
        new_node.dpass = 1
        xbar.insert_node(new_node, node)
        process_node(new_node, xbar)

    # If a node has multiple edges having it as a start node and not SOCKET_1N:
    elif node.node_type != NodeType.SOCKET_1N and len(node.ds) > 1:
        # (New node) Create SOCKET_1N node
        new_node = Node(name="s1n_" + str(len(xbar.nodes)),
                        node_type=NodeType.SOCKET_1N,
                        clock=xbar.clock)
        new_node.hpass = 1
        new_node.dpass = 2**len(node.ds) - 1
        xbar.insert_node(new_node, node)

        # (for loop) Repeat the algorithm with SOCKET_1N's other side node
        for edge in new_node.ds:
            process_node(edge.ds, xbar)

    return xbar


def process_pipeline(xbar):
    """Check if HOST, DEVICE has pipeline key and is True, then propagate it to end
    """
    for host in xbar.hosts:
        # go downstream and set the HReqPass at the first instance.
        # If it is async, skip.
        # If Socket 1N, set hpass to 1 and skip
        # If Socket M1, find position of the host and set 1 of the bit in hpass skip
        # If it is device, it means host and device are directly connected. Ignore now.

        # After process node is done, always only one downstream exists in any host node
        if host.pipeline == False:
            # No need to process, default is Pass the req/rsp
            continue

        dnode = host.ds[0].ds
        if dnode.node_type == NodeType.SOCKET_1N:
            dnode.hpass = 0
        elif dnode.node_type == NodeType.SOCKET_M1:
            idx = dnode.us.index(host.ds)
            dnode.hpass = dnode.hpass ^ (1 << idx)

    for device in xbar.devices:
        # go upstream and set DReq/RspPass at the first instance.
        # If it is async, skip
        # If Socket 1N, set dpass to the bit position and skip
        # If Socket M1, set dpass to 1 and skip
        # If it is host, ignore

        if device.pipeline == False:
            continue

        unode = device.us[0].us
        if unode.node_type == NodeType.SOCKET_1N:
            idx = unode.ds.index(device.us)
            unode.dpass = unode.dpass ^ (1 << idx)
        elif unode.node_type == NodeType.SOCKET_M1:
            unode.dpass = 0

    return xbar
