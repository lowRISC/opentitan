# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from .field_enums import HwAccess, SwAccess, SwRdAccess, SwWrAccess


class Field():
    """Field in a register.

    Field class contains necessary info to generate RTL code.
    It has two additional (tool generated) feidls, swrdaccess and swwraccess,
    which represent read and write type. This makes RTL generation code simpler.
    """
    name = ""  # required
    msb = 31  # required
    lsb = 0  # required
    resval = 0  # optional
    swaccess = SwAccess.NONE  # optional
    swrdaccess = SwRdAccess.NONE
    swwraccess = SwWrAccess.NONE
    hwaccess = HwAccess.HRO
    hwqe = False
    hwre = False

    def __init__(self):
        self.name = ""  # required
        self.msb = 31  # required
        self.lsb = 0  # required
        self.resval = 0  # optional
        self.swaccess = SwAccess.NONE  # optional
        self.swrdaccess = SwRdAccess.NONE
        self.swwraccess = SwWrAccess.NONE
        self.hwaccess = HwAccess.HRO
        self.hwqe = False
        self.hwre = False


class Reg():
    name = ""
    offset = 0
    hwqe = False
    hwre = False
    hwext = False  # External register
    resval = 0
    dvrights = "RO"  # Used by UVM REG only
    regwen = ""
    fields = []
    width = 0  # indicate register size

    def __init__(self):
        self.name = ""
        self.offset = 0
        self.hwqe = False
        self.hwre = False
        self.hwext = False  # External register
        self.resval = 0
        self.dvrights = "RO"  # Used by UVM REG only
        self.regwen = ""
        self.fields = []
        self.width = 0


class MultiReg(Reg):
    param = ""
    regs = []

    def __init__(self):
        super.__init__(self)
        self.param = ""
        self.regs = []


class Window():
    base_addr = 0
    limit_addr = 0
    n_bits = 0

    def __init__(self):
        self.base_addr = 0
        self.limit_addr = 0
        self.n_bits = 0


class Block():
    width = 32
    addr_width = 12
    base_addr = 0
    name = ""
    regs = []
    wins = []
    blocks = []
    params = []

    def __init__(self):
        self.width = 32
        self.addr_width = 12
        self.base_addr = 0
        self.name = ""
        self.regs = []
        self.wins = []
        self.blocks = []
        self.params = []
