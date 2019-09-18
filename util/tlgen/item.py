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


#Edges = List[Edge]
#Clocks = List[str]  # If length is more than one, should be exactly two

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
    # For non-socket node types, the below names are the same
    # For socket node types, name refers to the number of connections, e.g s1n_14
    # while sname refers to the node it is most related to, e.g unode for 1n, dnode for m1
    name = ""  # instance name of the node: str
    sname = "" # associated string name of the node: str

    # node_type: NodeType
    clocks = []  # Clocks  # Clock domain of the node
    # e.g. async_fifo in : clk_core , out : clk_main

    # If NodeType is Socket out from 1:N then address steering is used
    # But this value is also propagated up to a Host from multiple Devices
    # Device Node should have address_from, address_to
    address_from = 0  #: int
    address_to = 0  #: int

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

    def __init__(self, name, node_type, clock, sname=None):
        self.name = name
        self.sname = name if sname is None else sname
        self.node_type = node_type
        self.clocks = [clock]
        self.us = []
        self.ds = []
