# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code representing the entire chip for reggen'''

from typing import Dict, List, Optional, Tuple, Union

from reggen.ip_block import IpBlock
from reggen.params import ReggenParams
from reggen.reg_block import RegBlock
from reggen.window import Window

_IFName = Tuple[str, Optional[str]]
_Triple = Tuple[int, str, IpBlock]


class Top:
    '''An object representing the entire chip, as seen by reggen.

    This contains instances of some blocks (possibly multiple instances of each
    block), starting at well-defined base addresses. It may also contain some
    windows. These are memories that don't have their own comportable IP (so
    aren't defined in a block), but still take up address space.

    '''

    def __init__(self,
                 regwidth: int,
                 blocks: Dict[str, IpBlock],
                 instances: Dict[str, str],
                 if_addrs: Dict[Tuple[str, Optional[str]], int],
                 windows: List[Window],
                 attrs: Dict[str, str]):
        '''Class initializer.

        regwidth is the width of the registers (which must match for all the
        blocks) in bits.

        blocks is a map from block name to IpBlock object.

        instances is a map from instance name to the name of the block it
        instantiates. Every block name that appears in instances must be a key
        of blocks.

        if_addrs is a dictionary that maps the name of a device interface on
        some instance of some block to its base address. A key of the form (n,
        i) means "the device interface called i on an instance called n". If i
        is None, this is an unnamed device interface. Every instance name (n)
        that appears in connections must be a key of instances.

        windows is a list of windows (these contain base addresses already).

        attrs is a map from instance name to attr field of the block

        '''

        self.regwidth = regwidth
        self.blocks = blocks
        self.instances = instances
        self.if_addrs = if_addrs
        self.attrs = attrs

        self.window_block = RegBlock(regwidth, ReggenParams())

        # Generate one list of base addresses and objects (with each object
        # either a block name and interface name or a window). While we're at
        # it, construct inst_to_block_name and if_addrs.
        merged = []  # type: List[Tuple[int, Union[_IFName, Window]]]
        for full_if_name, addr in if_addrs.items():
            merged.append((addr, full_if_name))

            inst_name, if_name = full_if_name

            # The instance name must match some key in instances, whose value
            # should in turn match some key in blocks.
            assert inst_name in instances
            block_name = instances[inst_name]
            assert block_name in blocks

            # Check that if_name is indeed the name of a device interface for
            # that block.
            block = blocks[block_name]
            assert block.bus_interfaces.has_interface(False, if_name)

        for window in sorted(windows, key=lambda w: w.offset):
            merged.append((window.offset, window))
            self.window_block.add_window(window)

        # A map from block name to the list of its instances. These instances
        # are listed in increasing order of the lowest base address of one of
        # their interfaces. The entries are added into the dict in the same
        # order, so an iteration over items() will give blocks ordered by their
        # first occurrence in the address map.
        self.block_instances = {}  # type: Dict[str, List[str]]

        # Walk the merged list in order of increasing base address. Check for
        # overlaps and construct block_instances.
        offset = 0
        for base_addr, item in sorted(merged, key=lambda pr: pr[0]):
            # Make sure that this item doesn't overlap with the previous one
            assert offset <= base_addr, item

            if isinstance(item, Window):
                addrsep = (regwidth + 7) // 8
                offset = item.next_offset(addrsep)
                continue

            inst_name, if_name = item
            block_name = instances[inst_name]
            block = blocks[block_name]

            lst = self.block_instances.setdefault(block_name, [])
            if inst_name not in lst:
                lst.append(inst_name)

            # This should be guaranteed by the fact that we've already checked
            # the existence of a device interface.
            assert if_name in block.reg_blocks
            reg_block = block.reg_blocks[if_name]

            offset = base_addr + reg_block.offset
