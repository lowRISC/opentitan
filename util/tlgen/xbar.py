# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
from typing import Any, List, Tuple

from .item import Edge, Node, Host, Device, AsyncFifo, Socket1N, SocketM1


class Xbar:
    """Xbar contains configurations to generate TL-UL crossbar.
    """
    def __init__(self) -> None:
        self.clock = ""  # str  # primary clock of xbar
        self.reset = ""  # str  # primary reset of xbar
        self.name = ""  # str  # e.g. "main" --> main_xbar
        self.ip_path = ""  # additional path to generated rtl/dv folders: outdir/ip_path/rtl

        self.nodes: List[Node] = []
        self.edges: List[Edge] = []
        self.clocks: List[Any] = []
        self.resets: List[Any] = []

    def get_node(self, node: str) -> Node:
        result = [x for x in self.nodes if x.name == node]
        if len(result) != 1:
            raise  # Exception

        return result[0]

    @property
    def hosts(self) -> List[Host]:
        return [x for x in self.nodes if isinstance(x, Host)]

    @property
    def devices(self) -> List[Device]:
        return [x for x in self.nodes if isinstance(x, Device)]

    @property
    def socket_1ns(self) -> List[Socket1N]:
        return [x for x in self.nodes if isinstance(x, Socket1N)]

    def get_downstream_device(self, node: Node) -> Device:
        if isinstance(node, Device):
            return node

        if len(node.ds) == 0:
            log.error(
                "Node (%s) doesn't have downstream Node: US(%s), DS(%s)" %
                (node.name, ' '.join(map(repr, node.us)), ' '.join(
                    map(repr, node.ds))))
        return self.get_downstream_device(node.ds[0].ds)

    def get_downstream_device_from_edge(self, edge: Edge) -> Device:
        return self.get_downstream_device(edge.ds)

    def get_leaf_from_s1n(self, node: Node, idx: int) -> Device:
        """ get end-device node from Socket_1n's Downstream port

        Current implementation can't have multiple devices under the tree of
        one downstream port in Socket_1N
        """
        return self.get_downstream_device(node.ds[idx].ds)

    def get_s1n_if_exist(self, node: Node) -> Node:
        """ return SOCKET_1N if exists down from the node, if not return itself
        """
        if isinstance(node, Device):
            log.error("get_s1n_if_exist hits DEVICE type (unexpected)")
            return node
        if isinstance(node, Socket1N):
            return node
        return self.get_s1n_if_exist(node.ds[0].ds)

    def get_leaf_from_node(self, node: Node, idx: int) -> Node:
        """ get end device node from any node, idx is given to look down.
        """
        num_dev = len(self.get_s1n_if_exist(node).ds)
        if idx >= num_dev:
            log.error(
                "given index is greater than number of devices under the node")

        return self.get_leaf_from_s1n(self.get_s1n_if_exist(node), idx)

    def get_devices_from_host(self, host: Node) -> List[Device]:
        devices = list(
            map(self.get_downstream_device_from_edge,
                self.get_s1n_if_exist(host).ds))

        return devices

    def get_addr(self, device: Node) -> Tuple[int, int]:
        if not isinstance(device, Device):
            log.error("get_addr receives non DEVICE type node")

        return (device.address_from, device.address_to)

    def connect_nodes(self, u_node: str, d_node: str) -> bool:
        # Create edges between Nodes
        # Return false if Nodes aren't exist or same connection exists
        upNode = self.get_node(u_node)
        dnNode = self.get_node(d_node)

        edge = Edge(upNode, dnNode)

        if any([
                e.us.name == edge.us.name and e.ds.name == edge.ds.name
                for e in self.edges
        ]):
            return False

        self.edges.append(edge)

        upNode.ds.append(edge)
        dnNode.us.append(edge)

        return True

    def insert_node(self, new_node: Node, node: Node) -> 'Xbar':
        if isinstance(new_node, AsyncFifo):
            if isinstance(node, Host):
                # Insert node to downstream
                edge = Edge(node, new_node)
                new_node.ds = node.ds
                node.ds = [edge]
                new_node.us = [edge]
                self.nodes.append(new_node)
                self.edges.append(edge)
                for e in new_node.ds:
                    # replace us to new_node
                    e.us = new_node
            elif isinstance(node, Device):
                # insert node to upstream
                edge = Edge(new_node, node)
                new_node.us = node.us
                new_node.ds = node.ds
                node.us = [edge]
                new_node.ds = [edge]
                self.nodes.append(new_node)
                self.edges.append(edge)
                for e in new_node.us:
                    # replace us to new_node
                    e.ds = new_node
            else:
                raise
        elif isinstance(new_node, SocketM1):
            # Revise every upstream
            edge = Edge(new_node, node)
            new_node.us = node.us
            node.us = [edge]
            new_node.ds = [edge]
            self.nodes.append(new_node)
            self.edges.append(edge)
            for e in new_node.us:
                e.ds = new_node

        elif isinstance(new_node, Socket1N):
            # Revise every downstream
            edge = Edge(node, new_node)
            new_node.ds = node.ds
            node.ds = [edge]
            new_node.us = [edge]
            # TODO: add new_node.us logic
            self.nodes.append(new_node)
            self.edges.append(edge)
            for e in new_node.ds:
                e.us = new_node
        else:
            # Caller passes HOST or DEVICE as a new node. Error!
            log.error(
                "Xbar.insert_node is called with HOST or DEVICE: %s. Ignored" %
                (new_node.name))

        return self

    def repr_tree(self, node: Node, indent: int) -> str:
        """string format of tree connection from node to devices

        Desired output:
        host_a
          -> asf_nn
            -> s1n_nn
              -> sm1_mm
                -> device_c
              -> sm1_nn
                -> device_b

        """
        out = "// "
        if indent != 0:
            # not First
            out += ' ' * indent + '-> '

        out += node.name

        if not isinstance(node, Device):
            # still more nodes exist under this node
            for ds in node.ds:
                out += '\n'
                out += self.repr_tree(ds.ds, indent + 2)

        return out
