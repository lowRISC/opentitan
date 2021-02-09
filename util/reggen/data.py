# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from collections import OrderedDict
import re

from .multi_register import MultiRegister
from .register import Register


# helper funtion that strips trailing _number (used as multireg suffix) from name
# TODO: this is a workaround, should solve this in validate.py
def get_basename(name):
    match = re.search(r'_[0-9]+$', name)
    assert match
    assert match.start() > 0
    return name[0:match.start()]


class Block():
    def __init__(self):
        self.width = 32
        self.addr_width = 12
        # Key is instance name
        self.base_addr = OrderedDict()
        self.name = ""
        self.hier_path = ""
        self.regs = []
        self.wins = []
        self.blocks = []
        self.params = []
        self.tags = []

    def get_regs_flat(self):
        """Returns flattened register list
        """
        regs = []
        for r in self.regs:
            if isinstance(r, Register):
                regs.append(r)
            else:
                assert isinstance(r, MultiRegister)
                regs += r.regs

        return regs

    def get_n_bits(self, bittype=["q"]):
        """Returns number of bits in this block (including all multiregs and
        fields). By default this function counts read data bits (bittype "q"),
        but other bits such as "d", qe", "re", "de" can be counted as well by
        specifying them in the bittype list argument.
        """
        n_bits = 0
        for r in self.regs:
            n_bits += r.get_n_bits(bittype)
        return n_bits

    def get_n_regs_flat(self):
        return len(self.get_regs_flat())
