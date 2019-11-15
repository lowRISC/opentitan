# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Data Structure in Register Generation
"""

import logging as log
from copy import deepcopy
from textwrap import indent

from .field_enums import HwAccess, SwAccess, SwRdAccess, SwWrAccess

from typing import List


def find_name_of_reg(regs, name):
    for r in regs:
        if r.name == name:
            return r
        if isinstance(r, MultiReg) and len(r.regs) != 0:
            v = find_name_of_reg(r.regs, name)
            if v != None:
                return v

    return None


class Block():
    """IP Block

    Block contains list of Reg instances(including MultiReg)
    """
    name = ""
    regs = []
    params = []  # Parameter list

    def get_reg(self, name) -> "Reg":
        """Search the list of registers and return if it finds the name
        """
        return find_name_of_reg(self.regs, name)

    def __str__(self) -> str:
        outstr = f"Block: {self.name}\n"
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
        outstr = f"Param:: Name: {self.name}\n"
        outstr += f"        Default: {self.default}\n"
        outstr += f"        Local: {self.local}\n"
        return outstr


class Size():
    """Size class

    Size class represents the constant part of the register offset.
    """
    numeric = 0
    ceil = {}
    params = {}

    def __init__(self):
        self.numeric = 0
        self.ceil = {}
        self.params = {}

    def __init__(self, params={}):
        self.params = {}

        if not "num" in params:
            self.numeric = 0
        if not "ceil" in params:
            self.ceil = {}

        for k, v in params.items():
            if k == "num":
                self.numeric = v
                continue
            if k == "ceil":
                self.ceil = v
                continue
            log.info(f"Param {k} Value {v}")
            self.params[k] = v

    # TODO: def unroll_size(params):
    def __str__(self):
        outstr = ""
        if self.numeric != 0 or (len(self.ceil.items()) +
                                 len(self.params.items()) == 0):
            outstr += f"0x{self.numeric:X}"

        # ceil
        #if "div" in v.params:
        #    # Ceil
        #    value_str = "ceil({} * {} / 32) * 4".format(k, v.params["div"])
        #else:
        for k, vs in self.ceil.items():
            # v should be List[int]
            for v in vs:
                # TODO: Print ceil
                outstr += f" + ceil({k} * {v} / 32) * 4"

        for k, v in self.params.items():
            value_str = f"{k} * {v} "
            if outstr == "":
                outstr = value_str
            else:
                outstr += " + " + value_str

        return f"({outstr})"

    def __add__(self, o) -> "Size":
        """Adding two Offset instances
        """
        result = deepcopy(self)

        if isinstance(o, int):
            result.numeric += o
        else:
            #log.info("Value {}".format(str(o)))
            assert isinstance(o, Size)
            result.numeric += o.numeric
            #log.info("Adding items {}".format(o.params.items()))
            for k, v in o.params.items():
                if k in result.params:
                    result.params[k] += v
                else:
                    result.params[k] = v
            # TODO: Skipto handling here
            for k, v in o.ceil.items():
                assert isinstance(v, list)
                if k in result.ceil:
                    result.ceil[k].append(v)
                else:
                    result.ceil[k] = v
        return result

    def __radd__(self, o) -> "Offset":
        """Reverse add
        """
        return self + o


class Offset():
    """Offset class.

    Offset class combines the constant size and the variable * size.
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

    _const: Size = None
    # List[str] : Names of the loop
    # Reason to assign MultiReg not Size is that when elaborating, the Size
    # isn't yet calculated.
    _varnames: List[str] = []
    _var: List[Size] = []  # Eventually _varnames converted into list of Size
    skipto = (False, 0)

    def __init__(self):
        self._const = Size()
        self._varnames = []
        self._var = []
        self.skipto = (False, 0)

    def __init__(self, params={}):
        self.skipto = (False, 0)
        self._const = Size(params)
        self._varnames = []
        self._var = []

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

        outstr = str(self._const)

        if len(self._varnames) == 0:
            return f"({outstr})"

        if outstr != "":
            outstr += " + "

        variables = ['x', 'y', 'z']
        if len(self._var) != 0:
            # Can return actual size not the list of reg name
            for idx, mrs in enumerate(self._var):
                assert isinstance(mrs, Size)

                if idx != 0:
                    outstr += " + "

                outstr += variables[idx] + " * " + str(mrs)

            return f"({outstr})"

        # The size isn't yet calculated. Use _varnames
        for idx, lv in enumerate(self._varnames):
            assert isinstance(lv, str)

            log.info(f"MultiReg {lv} in loop")
            if idx != 0:
                outstr += " + "

            outstr += variables[idx] + " * " + str(lv) + ".inner_size"

        return f"({outstr})"

    def __deepcopy__(self, memo):
        #log.info("Deepcopy memo: {} / self {}".format(str(memo), str(self)))
        offset = Offset()
        offset.skipto = deepcopy(self.skipto)
        offset._const = deepcopy(self._const)

        # offset._varnames = self._varnames  # MultiReg pointer should be propagated
        offset._varnames = deepcopy(self._varnames)
        return offset

    def __add__(self, o) -> "Offset":
        """Adding two Offset instances
        """
        offset = deepcopy(self)

        if isinstance(o, int):
            offset._const += o
        else:
            #log.info("Value {}".format(str(o)))
            assert isinstance(o, Size)
            offset._const += o
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
    _size: Size = None
    hwqe = False
    hwre = False
    hwext = False  # External register

    regwen = None
    fields = []
    width = 0
    parents = []

    def __init__(self):
        self.name = ""
        self.offset = Offset()
        self._size = Size({"num": 4})
        self.parents = []

    def is_multireg(self):
        return isinstance(self, MultiReg)

    def __str__(self):
        outstr = f"Reg:: Name: {self.name}\n"
        outstr += f"      Offset: {self.offset}\n"
        for f in self.fields:
            outstr += indent(str(f), "  ")

        return outstr

    @property
    def size(self) -> Size:
        """Return the register block size including the nested size too
        """
        return self._size  # Return constant 4B size

    @size.setter
    def size(self, v):
        if isinstance(v, int):
            log.info(f"Reg {self.name} adding integer {v} to size")
            self._size.numeric = v
        else:
            log.info(f"Reg {self.name} adding Offset {v} to size")
            assert isinstance(v, Offset)
            self._size = v

    @property
    def inner_size(self) -> Size:
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
    parents = []
    width = 0

    size_calculated = False

    def __init__(self, params={}):
        self.name = ""
        self.offset = Offset({"num": 0})
        self._size = Size({"num": 0})
        self.size_calculated = False
        self.parents = []

    def __str__(self):
        outstr = f"MultiReg:: Name: {self.name} @ {self.count}\n"
        outstr += f"           Offset: {self.offset}\n"
        outstr += f"           Size: {self.size}\n"
        outstr += f"           Inner Size: {self.inner_size}\n"
        for r in self.regs:
            outstr += indent(str(r), "  ")

        return outstr

    def update_size(self):
        if self.regs:
            self._size.params[self.count] = sum([x.size for x in self.regs])
            #log.info("{} updating the size {}".format(self.name, self._size))
        elif self.fields:
            # Field multi register
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

            self._size.ceil[self.count] = [f_size]
            #log.info("{} updating the size based on field {}".format(
            #    self.name, self._size))

    @property
    def size(self) -> Size:
        """Return MultiReg size including the nested registers too

        Shall return the reference of the class member
        """
        if not self.size_calculated:
            self.update_size()

        return self._size

    @property
    def inner_size(self) -> Size:
        """Return the inner loop size of MultiReg.

        Inner Size is the size of MultiReg with an assumption of the
        count value is 1.
        """
        if not self.size_calculated:
            self.update_size()

        if self.regs:
            return self._size.params[self.count]

        # field
        if self.count in self._size.ceil:
            return self._size.ceil[self.count]

        log.info(f"The inner_size of {self.name} isn't yet fully calculated")
        return Size()


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
        return f"F[{self.msb}:{self.lsb}] {self.name}\n"
