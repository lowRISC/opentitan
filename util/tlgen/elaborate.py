# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log

from .item import Node, AsyncFifo, Host, SocketM1, Socket1N
from .xbar import Xbar


def elaborate(xbar: Xbar) -> bool:
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

    # Pipeline
    process_pipeline(xbar)

    # Build address map
    # Each socket_1n should have address map

    return True


def process_node(node: Node, xbar: Xbar) -> Xbar:
    """Process each node based on the following algorithm.

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
       d. (for loop) Repeat the algorithm with SOCKET_1N's other side node.
    """

    # If a node has different clock from main clock and not ASYNC_FIFO:
    if node.clocks[0] != xbar.clock and not isinstance(node, AsyncFifo):
        # (New Node) Create ASYNC_FIFO node
        new_node = AsyncFifo(name="asf_" + str(len(xbar.nodes)),
                             clock=xbar.clock,
                             reset=xbar.reset)

        # if node is HOST, host clock synchronizes into xbar domain
        # if node is DEVICE, xbar synchronizes into device clock domain
        if isinstance(node, Host):
            new_node.clocks.insert(0, node.clocks[0])
            new_node.resets.insert(0, node.resets[0])
        else:
            new_node.clocks.append(node.clocks[0])
            new_node.resets.append(node.resets[0])

        xbar.insert_node(new_node, node)

        process_node(new_node, xbar)

    # If a node has multiple edges having it as a end node and not SOCKET_M1:
    elif len(node.us) > 1 and not isinstance(node, SocketM1):
        # (New node) Create SOCKET_M1 node
        new_node = SocketM1(hwidth=len(node.us),
                            name="sm1_" + str(len(xbar.nodes)),
                            clock=xbar.clock,
                            reset=xbar.reset)

        xbar.insert_node(new_node, node)
        process_node(new_node, xbar)

    # If a node has multiple edges having it as a start node and not SOCKET_1N:
    elif len(node.ds) > 1 and not isinstance(node, Socket1N):
        # (New node) Create SOCKET_1N node
        new_node = Socket1N(dwidth=len(node.ds),
                            name="s1n_" + str(len(xbar.nodes)),
                            clock=xbar.clock,
                            reset=xbar.reset)

        xbar.insert_node(new_node, node)

        # (for loop) Repeat the algorithm with SOCKET_1N's other side node
        for edge in new_node.ds:
            process_node(edge.ds, xbar)

    return xbar


def process_pipeline(xbar):
    """Check if HOST, DEVICE has settings different from default, then propagate it to end
    """
    for host in xbar.hosts:
        # go downstream and change the HReqPass/Depth at the first instance.
        # If it is async, skip.
        # If Socket 1N,
        #    if pipeline True and bypass false, set hpass to 0
        #    if pipeline is False, set depth to 0
        # If Socket M1, find position of the host and follow procedure above
        # If it is device, it means host and device are directly connected. Ignore now.

        log.info("Processing pipeline for host {}".format(host.name))

        fifo_pass = host.req_fifo_pass or host.rsp_fifo_pass

        # FIFO present with no passthrough option
        # FIFO present with passthrough option
        # FIFO not present and full passthrough
        full_fifo = False
        fifo_passthru = False
        full_passthru = True
        if host.pipeline is True and fifo_pass is False:
            full_fifo = True

        elif host.pipeline is True and fifo_pass is True:
            fifo_passthru = True

        elif host.pipeline is False:
            full_passthru = True

        dnode = host.ds[0].ds

        if isinstance(dnode, AsyncFifo):
            continue

        req_pass = 1 if host.req_fifo_pass else 0
        rsp_pass = 1 if host.rsp_fifo_pass else 0
        if isinstance(dnode, Socket1N):
            if full_fifo:
                dnode.hreq_pass = 0
                dnode.hrsp_pass = 0
                dnode.hdepth = 1
            elif fifo_passthru:
                dnode.hreq_pass = req_pass
                dnode.hrsp_pass = rsp_pass
                dnode.hdepth = 1
            elif full_passthru:
                dnode.hreq_pass = 1
                dnode.hrsp_pass = 1
                dnode.hdepth = 0

            log.info(
                "Finished processing socket1n {}, req pass={}, rsp pass={}, depth={}".format(
                    dnode.name, dnode.hreq_pass, dnode.hrsp_pass, dnode.hdepth))

        elif isinstance(dnode, SocketM1):
            idx = dnode.us.index(host.ds[0])

            # first clear out entry
            dnode.hreq_pass = dnode.hreq_pass & ~(1 << idx)
            dnode.hreq_pass = dnode.hreq_pass & ~(1 << idx)
            if full_fifo:
                log.info("fifo present no bypass")
                dnode.hdepth = dnode.hdepth | (1 << idx * 4)
            elif fifo_passthru:
                log.info("fifo present with bypass")
                dnode.hreq_pass = dnode.hreq_pass | (req_pass << idx)
                dnode.hreq_pass = dnode.hrsp_pass | (rsp_pass << idx)
                dnode.hdepth = dnode.hdepth | (1 << idx * 4)
            elif full_passthru:
                log.info("fifo not present")
                dnode.hreq_pass = dnode.hreq_pass | (1 << idx)
                dnode.hreq_pass = dnode.hrsp_pass | (1 << idx)
                dnode.hdepth = dnode.hdepth & ~(0xF << idx * 4)

            log.info(
                "Finished processing socketm1 {}, req pass={}, rsp pass={}, depth={}".format(
                    dnode.name, dnode.hreq_pass, dnode.hrsp_pass, dnode.hdepth))

    for device in xbar.devices:
        # go upstream and set DReq/RspPass at the first instance.
        # If it is async, skip
        # If Socket M1
        #    If pipeline True and bypass False, set dpass to 0
        #    If pipeline False, set depth to 0
        # If Socket 1N, find position of the device and follow procedure above
        # If it is host, ignore

        log.info("Processing pipeline for device {}".format(device.name))

        # FIFO present with no passthrough option
        # FIFO present with passthrough option
        # FIFO not present and full passthrough
        fifo_pass = device.req_fifo_pass or device.rsp_fifo_pass
        full_fifo = False
        fifo_passthru = False
        full_passthru = True
        if device.pipeline is True and fifo_pass is False:
            full_fifo = True

        elif device.pipeline is True and fifo_pass is True:
            fifo_passthru = True

        elif device.pipeline is False:
            full_passthru = True

        unode = device.us[0].us

        if isinstance(unode, AsyncFifo):
            continue

        req_pass = 1 if device.req_fifo_pass else 0
        rsp_pass = 1 if device.rsp_fifo_pass else 0
        if isinstance(unode, Socket1N):
            idx = unode.ds.index(device.us[0])

            # first clear out entry
            unode.dreq_pass = unode.dreq_pass & ~(1 << idx)
            unode.drsp_pass = unode.drsp_pass & ~(1 << idx)
            if full_fifo:
                unode.ddepth = unode.ddepth | (1 << idx * 4)
            elif fifo_passthru:
                unode.dreq_pass = unode.dreq_pass | (req_pass << idx)
                unode.drsp_pass = unode.drsp_pass | (rsp_pass << idx)
                unode.ddepth = unode.ddepth | (1 << idx * 4)
            elif full_passthru:
                unode.dreq_pass = unode.dreq_pass | (1 << idx)
                unode.drsp_pass = unode.drsp_pass | (1 << idx)
                unode.ddepth = unode.ddepth & ~(0xF << idx * 4)

            log.info("Finished processing socket1n {}, req pass={:x}, req pass={:x} depth={:x}".
                     format(unode.name, unode.dreq_pass, unode.drsp_pass, unode.ddepth))

        elif isinstance(unode, SocketM1):
            if full_fifo:
                log.info("Fifo present with no passthrough")
                unode.dreq_pass = 0
                unode.drsp_pass = 0
                unode.ddepth = 1
            elif fifo_passthru:
                log.info("Fifo present with passthrough")
                unode.dreq_pass = req_pass
                unode.drsp_pass = rsp_pass
                unode.ddepth = 1
            elif full_passthru:
                log.info("No Fifo")
                unode.dreq_pass = 1
                unode.drsp_pass = 1
                unode.ddepth = 0

            log.info("Finished processing socketm1 {}, req pass={:x}, rsp pass={:x}, depth={:x}".
                     format(unode.name, unode.dreq_pass, unode.drsp_pass, unode.ddepth))

    return xbar
