# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Data Structure in Register Generation
"""

import logging as log
from copy import deepcopy
from textwrap import indent

from .field_enums import HwAccess, SwAccess, SwRdAccess, SwWrAccess


class Block():
    """IP Block

    Block contains list of Reg instances(including MultiReg)
    """
    name = ""
    regs = []
    params = []  # Parameter list

    def __str__(self) -> str:
        outstr = "Block: {}\n".format(self.name)
        if len(self.params) > 0:
            outstr += "  Parameters\n"
            for p in self.params:
                outstr += indent(str(p), "    ")

        if len(self.regs) > 0:
            outstr += "  Registers\n"
            for r in self.regs:
                outstr += indent(str(r), "    ")

        return outstr


class Param():
    """Parameter used in the registers
    """
    name = ""
    default = 1
    value = 1
    local = False

    def __init__(self, name="", default=1, local=False):
        self.name = name
        self.default = default
        self.local = local

    def __str__(self):
        outstr = "Param:: Name: {}\n".format(self.name)
        outstr += "        Default: {}\n".format(self.default)
        outstr += "        Local: {}\n".format(self.local)
        return outstr


class Offset():
    """Offset class.

    Offset class represents the constant parts of the register offset.
    For instance, if a Reg inside MultiReg, its constant part is the start
    address of the multureg with the constant offset of a Reg relative to the
    start of the multireg loop.
    """

    # param Dictionary structure
    #   {
    #       "num": int,
    #       "ParamA": Offset, # recursive
    #       ...
    #   }
    #
    #   TODO: Revise below description with clear example.
    #   The value of Param is always list structure. It represents the
    #   combination of, size of the MultiReg and/or constant offset value
    params = {}
    skipto = (False, 0)

    def __init__(self):
        self.params = {"num": 0}
        self.skipto = (False, 0)

    def __init__(self, params={}):
        self.skipto = (False, 0)
        self.params = {}

        if not "num" in params:
            self.params["num"] = 0
        for k, v in params.items():
            log.info("Param {} Value {}".format(k, v))
            self.params[k] = v

    def unroll_offset(self, params={}):
        """Get the hard-coded offset from given params

        This function shall not be used while generating parameterized register
        module. This function shall be used to generate top-level specific reg
        table.
        """

        offset_hex = 0
        # TODO: Check if all params are addressed

        return offset_hex

    def __str__(self):
        outstr = ""
        if self.params["num"] != 0:
            outstr += "0x{:X}".format(self.params["num"])

        remained = deepcopy(self.params)
        del remained["num"]
        #log.info("Removed `num` {} from {}".format(remained, self.params))

        if len(remained.items()) == 0:
            # return as it is for integer value only
            return outstr if outstr != "" else "0x0"

        for k, v in remained.items():
            if k == "div":
                # Handled out there
                continue
            if "div" in v.params:
                # Ceil
                value_str = "ceil({} * {} / 32) * 4".format(k, v.params["div"])
            else:
                value_str = "{} * {} ".format(k, v)
            if outstr == "":
                outstr = value_str

            else:
                outstr += " + " + value_str
        return "({})".format(outstr)

    #def __deepcopy__(self, memo):
    #    #log.info("Deepcopy memo: {} / self {}".format(str(memo), str(self)))
    #    #offset = Offset()
    #    #offset.params = deepcopy(self.params)
    #    #offset.skipto = deepcopy(self.skipto)
    #    #return offset

    def __add__(self, o) -> "Offset":
        """Adding two Offset instances
        """
        offset = deepcopy(self)

        if isinstance(o, int):
            offset.params["num"] += o
        else:
            assert isinstance(o, Offset)
            #log.info("Adding items {}".format(o.params.items()))
            for k, v in o.params.items():
                if k in offset.params:
                    offset.params[k] += v
                else:
                    offset.params[k] = v
            # TODO: Skipto handling here
        return offset

    def __radd__(self, o) -> "Offset":
        """Reverse add
        """
        return self + o


class Reg():
    """Register classs

    offset: Dict of the register offset, It has parameters as keys, including
    `num` key as hard offset.
    """
    name = ""
    offset: Offset = None
    _size: Offset = None
    hwqe = False
    hwre = False
    hwext = False  # External register

    regwen = None
    fields = []
    width = 0

    def __init__(self):
        self.name = ""
        self.offset = Offset()
        self._size = Offset({"num": 4})

    def is_multireg(self):
        return isinstance(self, MultiReg)

    def __str__(self):
        outstr = "Reg:: Name: {}".format(self.name) + "\n"
        outstr += "      Offset: {}".format(str(self.offset)) + "\n"
        for f in self.fields:
            outstr += indent(str(f), " \\")

        return outstr

    @property
    def size(self) -> Offset:
        """Return the register block size including the nested size too
        """
        return self._size  # Return constant 4B size

    @size.setter
    def size(self, v):
        if isinstance(v, int):
            log.info("Reg {} adding integer {} to size".format(self.name, v))
            self._size.params["num"] = v
        else:
            log.info("Reg {} adding Offset {} to size".format(self.name, v))
            assert isinstance(v, Offset)
            self._size = v

    @property
    def inner_size(self) -> Offset:
        """Return inner loop size of the register. Not used in Reg
        """
        return self._size

    @property
    def field_size(self) -> int:
        """Return field max size
        """
        max_size = max([x.msb + 1 for x in self.fields])
        return max_size


class MultiReg(Reg):
    """ Extension of Reg
    """
    name = ""
    count = ""  # Parameter
    offset = {}
    hwqe = False
    hwre = False
    hwext = False

    regwen = None
    regs = []
    fields = []
    width = 0

    def __init__(self, params={}):
        self.name = ""
        self.offset = Offset({"num": 0})
        self._size = Offset({"num":
                             0})  # Empty as its size is not determined yet

    def __str__(self):
        outstr = "MultiReg:: Name: {} @ {}".format(self.name,
                                                   self.count) + "\n"
        outstr += "           Offset: {}".format(str(self.offset)) + "\n"
        outstr += "           Size: {}".format(str(self.size)) + "\n"
        outstr += "           Inner Size: {}".format(str(
            self.inner_size)) + "\n"
        for r in self.regs:
            outstr += indent(str(r), " \\")

        return outstr

    def update_size(self):
        if self.regs:
            self._size.params[self.count] = sum(
                [x.inner_size for x in self.regs])
            log.info("{} updating the size {}".format(self.name, self._size))
        elif self.fields:
            # Field multi register
            offset = Offset()
            # Can do with pow & log function but make it cases
            if self.field_size <= 1:
                f_size = 1
            elif self.field_size <= 2:
                f_size = 2
            elif self.field_size <= 4:
                f_size = 4
            elif self.field_size <= 8:
                f_size = 8
            elif self.field_size <= 16:
                f_size = 16
            else:
                f_size = 32

            offset.params["div"] = f_size
            self._size.params[self.count] = offset
            log.info("{} updating the size based on field {}".format(
                self.name, self._size))

    @property
    def size(self) -> Offset:
        """Return MultiReg size including the nested registers too

        Shall return the reference of the class member
        """
        self.update_size()

        return self._size

    @property
    def inner_size(self) -> Offset:
        """Return the inner loop size of MultiReg.

        Inner Size is the size of MultiReg with an assumption of the
        count value is 1.
        """
        self.update_size()

        return self._size.params[self.count]


class Field():
    """Field in a Reg
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
    hwext = False

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
        self.hwext = False

    def __str__(self):
        outstr = ""
        outstr += "F[{}:{}] {}\n".format(self.msb, self.lsb, self.name)
        return outstr
