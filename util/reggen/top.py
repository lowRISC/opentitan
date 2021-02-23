# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code representing the entire chip for reggen'''

from typing import Dict, List, Tuple, Union

from .block import Block
from .ip_block import IpBlock
from .params import Params
from .reg_block import RegBlock
from .window import Window

_Triple = Tuple[int, str, IpBlock]


class Top(Block):
    def __init__(self,
                 regwidth: int,
                 blocks: Dict[int, Tuple[str, IpBlock]],
                 windows: List[Window]):
        super().__init__('chip',
                         regwidth,
                         RegBlock(regwidth, Params()))

        self.regwidth = regwidth

        addrsep = (regwidth + 7) // 8

        # A list of blocks. Each appears just once, even if it has multiple instances
        self.blocks = []  # type: List[IpBlock]

        # A dictionary mapping instance name to a pair (base_addr, block)
        self.by_inst_name = {}  # type: Dict[str, Tuple[int, IpBlock]]

        # A list of tuples: (addr, instance_name, block) in increasing order of
        # address.
        self.instances = []  # type: List[_Triple]

        # A dictionary mapping block name to instances of that block. Items are
        # pairs (addr, instance_name, block).
        self.block_name_to_instances = {}  # type: Dict[str, List[_Triple]]

        # Generate one big map from base address to object (with each value
        # either a pair (instance_name, block) or a window).
        addr_to_obj = {}  # type: Dict[int, Union[Tuple[str, IpBlock], Window]]
        for addr, pr in blocks.items():
            addr_to_obj[addr] = pr
        for window in windows:
            addr_to_obj[window.offset] = window

        # Now walk this big map again, constructing the two views on the blocks
        # and adding the windows as we go but checking for overlaps the whole
        # time.
        offset = 0
        for base_addr in sorted(addr_to_obj.keys()):
            obj = addr_to_obj[base_addr]

            # Make sure that this block doesn't overlap with the previous one
            assert offset <= base_addr

            if isinstance(obj, Window):
                offset = obj.next_offset(addrsep)
                self.regs.add_window(obj)
            else:
                name, block = blocks[base_addr]

                if block.name not in self.block_name_to_instances:
                    self.blocks.append(block)

                assert name not in self.by_inst_name
                self.by_inst_name[name] = (base_addr, block)

                triple = (base_addr, name, block)
                self.instances.append(triple)
                insts = self.block_name_to_instances.setdefault(block.name, [])
                insts.append(triple)

                offset = base_addr + block.regs.offset
