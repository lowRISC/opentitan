# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from collections import OrderedDict
import re


# helper function that strips trailing _number (used as multireg suffix) from name
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
        self.reg_block = None
        self.blocks = []
        self.params = []
        self.tags = []
