# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Classes to represent the crossbar's dataflow graph."""

from typing import List, Tuple


class Edge:
    """A connection between two nodes.

    A node can be a host port, output of async_fifo, port in a socket,
    or a device port.
    """

    def __init__(self, us: 'Node', ds: 'Node'):
        """Create an edge between us and ds."""
        self.us = us
        self.ds = ds


class Node:
    """Base class representing a node in the data graph."""

    name: str = ""

    clocks: List[str] = []  # clock domains of the node. Should have at most 2.
    resets: List[str] = []  # resets of the node
    # e.g. async_fifo in : clk_core , out : clk_main

    # If NodeType is Socket out from 1:N then address steering is used
    # But this value is also propagated up to a Host from multiple Devices
    # A device Node should have address_from, address_to.
    #
    # Other nodes have this fields set to -1.
    address_from: int = -1
    address_to: int = -1
    addr_range: List[Tuple[int, int]] = []

    us: List[Edge] = []  # Number of Ports depends on the NodeType
    # 1 for Host, Device, 2 for Async FIFO, N for Sockets
    ds: List[Edge] = []

    # Req/Rsp FIFO. default False
    # when False, no storage element
    # when True, FIFO present with default depth, the "fifo_pass"
    # variables control whether a particular direction in the fifo
    # has the passthrough behvaior
    pipeline = True

    # FIFO passtru option. default True
    # If pipeline is false, these fields have no meaning
    # passthrough behavior refers to a FIFO passing the trasnaction
    # through if the FIFO is currently empty
    req_fifo_pass = True
    rsp_fifo_pass = True

    def __init__(self,
                 name: str,
                 clock: str,
                 reset: str):
        """Construct a node with the given name and main clock/reset."""
        self.name = name
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


class Host(Node):
    """A host node."""


class Device(Node):
    """A device node."""

    xbar: bool = False


class AsyncFifo(Node):
    """A node representing an async fifo."""


class Socket(Node):
    """A node representing a socket (1N or M1)."""

    hdepth: int
    hreq_pass: int
    hrsp_pass: int

    ddepth: int
    dreq_pass: int
    drsp_pass: int

    def __init__(self, hwidth: int, dwidth: int,
                 name: str, clock: str, reset: str):
        """Construct a socket with given host/device width."""
        super().__init__(name, clock, reset)
        self.hdepth = 0
        self.hreq_pass = 2 ** hwidth - 1
        self.hrsp_pass = 2 ** hwidth - 1
        self.ddepth = 0
        self.dreq_pass = 2 ** dwidth - 1
        self.drsp_pass = 2 ** dwidth - 1


class Socket1N(Socket):
    """A 1N socket."""

    def __init__(self, dwidth: int,
                 name: str, clock: str, reset: str):
        """Construct a 1N socket with given device width."""
        super().__init__(1, dwidth, name, clock, reset)


class SocketM1(Socket):
    """An M1 socket."""

    def __init__(self, hwidth: int,
                 name: str, clock: str, reset: str):
        """Construct a socket with given host width."""
        super().__init__(hwidth, 1, name, clock, reset)
