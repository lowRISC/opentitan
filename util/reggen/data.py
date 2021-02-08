# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from collections import OrderedDict

from .field import Field


# helper funtion that strips trailing _number (used as multireg suffix) from name
# TODO: this is a workaround, should solve this in validate.py
def get_basename(name):
    for (k, c) in enumerate(name[::-1]):
        if not str.isdigit(c):
            if c == "_":
                return name[0:len(name) - (k + 1)]
            else:
                break
    return ""


class Reg():
    def __init__(self, name=""):
        self.name = name
        self.offset = 0
        self.hwqe = False
        self.hwre = False
        self.hwext = False  # External register
        self.resval = 0
        self.dvrights = "RO"  # Used by UVM REG only
        self.regwen = ""
        self.fields = []
        self.width = 0
        self.ishomog = 0
        self.tags = []
        self.shadowed = False
        self.update_err_alert = ""  # Used by shadow reg DV
        self.storage_err_alert = ""  # Used by shadow reg DV

    def is_multi_reg(self):
        """Returns true if this is a multireg"""
        return False

    def get_n_bits(self, bittype=["q"]):
        """Returns number of bits in this register (including all multiregs and
        fields). By default this function counts read data bits (bittype "q"),
        but other bits such as "d", qe", "re", "de" can be counted as well by
        specifying them in the bittype list argument.
        """
        n_bits = 0
        for f in self.fields:
            if isinstance(f, Reg):
                n_bits += f.get_n_bits(bittype)
            else:
                n_bits += f.get_n_bits(self.hwext, bittype)
        return n_bits

    def get_fields_flat(self):
        """Returns a flat list of all the fields in this register"""
        ret = []
        for f in self.fields:
            if isinstance(f, Reg):
                ret += f.get_fields_flat()
            else:
                ret.append(f)

        return ret

    def get_field_flat(self, linear_idx):
        """Returns a specific field at a linear index position in
        the flattened field list"""
        fields_flat = self.get_fields_flat()
        return fields_flat[linear_idx]

    def get_n_fields_flat(self):
        """Returns the number of fields contained in the flat field list"""
        return len(self.get_fields_flat())

    def get_regs_flat(self):
        """Returns a flat list containing all
        registers and subregisters"""
        if isinstance(self.fields[0], Field):
            return [self]
        else:
            regs = []
            for r in self.fields:
                regs += r.get_regs_flat()
            return regs

    def get_reg_flat(self, linear_index):
        """Returns a specific register at a linear index position in
        the flattened regiser list"""
        regs_flat = self.get_regs_flat()
        return regs_flat[linear_index]

    def get_n_regs_flat(self):
        """Returns the number of registers contained in
        the flat register list"""
        return len(self.get_regs_flat())

    def get_nested_dims(self):
        """Recursively get dimensions of nested registers (outputs a list)"""
        # return length of flattened field array if this is a regular register,
        # or if this is the last multiregister level in a nested multiregister
        if not isinstance(self, MultiReg):
            dims = [len(self.get_fields_flat())]
        if isinstance(self, MultiReg) and\
           not isinstance(self.fields[0], MultiReg):
            if self.ishomog:
                dims = [len(self.get_fields_flat())]
            else:
                dims = [len(self.fields)]
        else:
            # nested multiregister case
            dims = [len(self.fields)] + self.fields[0].get_nested_dims()
        return dims

    def get_nested_params(self):
        """Recursively get parameters of nested registers (outputs a list)"""
        params = []
        if isinstance(self, MultiReg):
            params += [self.param]
        if isinstance(self.fields[0], MultiReg):
            params += self.fields[0].get_nested_params()
        return params


class MultiReg(Reg):
    def __init__(self, name):
        Reg.__init__(self, name)
        self.param = ""

    def is_multi_reg(self):
        """Returns true if this is a multireg"""
        return True


class Window():
    def __init__(self):
        self.base_addr = 0
        self.byte_write = 0
        self.limit_addr = 0
        self.n_bits = 0
        self.tags = []


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
            regs += r.get_regs_flat()
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

    def contains_multiregs(self):
        """Returns true if there are multiregs in this block
        """
        for r in self.regs:
            if isinstance(r, MultiReg):
                return True
        return False
