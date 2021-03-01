# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import Enum


class Edge:
    """Edge class contains the connection from a node to a node.

    a Node can be a host port, output of async_fifo, port in a socket,
    or a device port.
    """
    def __init__(self, us, ds):
        self.us = us
        self.ds = ds

    def __repr__(self):
        return "U(%s) D(%s)" % (self.us.name, self.ds.name)


# Edges = List[Edge]
# Clocks = List[str]  # If length is more than one, should be exactly two

# [UpstreamClock, DownstreamClock]


class NodeType(Enum):
    HOST = 1
    DEVICE = 2
    ASYNC_FIFO = 3
    SOCKET_1N = 4
    SOCKET_M1 = 5


class Node:
    """Node class is a port that communicates from/to other Node or TL-UL
    input/output.
    """

    name = ""  # name: str
    # node_type: NodeType
    clocks = []  # Clocks  # clock domains of the node
    resets = []  # Resets  # resets of the node
    # e.g. async_fifo in : clk_core , out : clk_main

    # If NodeType is Socket out from 1:N then address steering is used
    # But this value is also propagated up to a Host from multiple Devices
    # Device Node should have address_from, address_to
    # address_from = 0  #: int
    # address_to = 0  #: int
    addr_range = []

    us = []  # Edges  # Number of Ports depends on the NodeType
    # 1 for Host, Device, 2 for Async FIFO, N for Sockets
    ds = []  # Edges

    # Req/Rsp FIFO. default False
    # when False, FIFO fully passthrough, no storage element
    # when True, FIFO present with default depth, "pipeline_byp"
    # controls passthrough option
    pipeline = False

    # FIFO passtru option. default True
    pipeline_byp = True

    def __init__(self, name, node_type, clock, reset):
        self.name = name
        self.node_type = node_type
        self.clocks = [clock]
        self.resets = [reset]
        self.us = []
        self.ds = []
        self.addr_range = []

    def esc_name(self) -> str:
        '''Return an "escaped name" for this node

        This replaces '.' characters with '__'. Needed because the node name
        might be of the form inst_name.if_name (which isn't a valid symbol name
        in C or SystemVerilog)

        '''
        return self.name.replace('.', '__')
