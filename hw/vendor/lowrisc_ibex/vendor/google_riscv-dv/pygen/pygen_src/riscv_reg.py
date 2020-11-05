"""
Copyright 2020 Google LLC
Copyright 2020 PerfectVIPs Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
"""

import sys
import logging
import vsc
from importlib import import_module
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_instr_pkg import (
    pkg_ins, privileged_reg_t, reg_field_access_t, privileged_level_t)
rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")


# Light weight RISC-V register class library
# Base class for RISC-V register field
@vsc.randobj
class riscv_reg_field:
    def __init__(self):
        self.bit_width = 0
        self.reset_val = vsc.bit_t(rcs.XLEN)
        self.val = vsc.rand_bit_t(rcs.XLEN)
        self.access_type = vsc.enum_t(reg_field_access_t)
        self.hard_wired = vsc.bit_t(1)
        self.name = ""

    @vsc.constraint
    def zero_reserved_field_c(self):
        with vsc.implies(self.access_type == reg_field_access_t.WPRI):
            self.val == 0

    @vsc.constraint
    def hardwired_fld_c(self):
        with vsc.implies(self.hard_wired == 1):
            self.val == self.reset_val

    def convert2string(self):
        return pkg_ins.format_string("{} bit_width:{} val:{} type:{}".format(
            self, self.bit_width, hex(self.val), self.access_type))

    def post_randomize(self):
        mask = vsc.bit_t(rcs.XLEN, 2**rcs.XLEN - 1)
        mask = mask >> (rcs.XLEN - self.bit_width)
        self.val = mask & self.val


# Base class for RISC-V register
@vsc.randobj
class riscv_reg:
    def __init__(self):
        self.reg_name = vsc.enum_t(privileged_reg_t)
        self.offset = vsc.bit_t(12)
        self.privil_level = vsc.enum_t(privileged_level_t)
        self.val = vsc.bit_t(rcs.XLEN)
        self.fld = vsc.rand_list_t(vsc.attr(riscv_reg_field()))

    def init_reg(self, reg_name):
        self.reg_name = reg_name
        self.offset = reg_name.value

    def get_val(self):
        total_len = 0
        for i in range((len(self.fld) - 1), -1, -1):
            total_len += self.fld[i].bit_width
        if total_len != rcs.XLEN:
            for i in range((len(self.fld) - 1), -1, -1):
                logging.info(self.fld[i].convert2string())
            logging.critical("Total field length {} != XLEN {}".format(total_len, rcs.XLEN))
            sys.exit(1)
        self.val = 0
        for i in range((len(self.fld) - 1), -1, -1):
            self.val = (self.val << self.fld[i].bit_width) | self.fld[i].val
        return self.val

    def add_field(self, fld_name, bit_width, access_type, reset_val = 0):
        new_fld = riscv_reg_field()
        new_fld.bit_width = bit_width
        new_fld.access_type = access_type
        new_fld.reset_val = reset_val
        new_fld.name = fld_name
        self.fld.append(new_fld)  # insert(index, value) is not supported in PyVSC

    def set_field(self, fld_name, val, hard_wired = 0):
        for i in range((len(self.fld) - 1), -1, -1):
            if fld_name == self.fld[i].name:
                self.fld[i].val = val
                self.fld[i].hard_wired = hard_wired
                if hard_wired:
                    self.fld[i].reset_val = val
                return
        logging.critical("Cannot match found field {}".format(fld_name))
        sys.exit(1)

    def get_field_by_name(self, fld_name):
        for i in range((len(self.fld) - 1), -1, -1):
            if fld_name == self.fld[i].name:
                return self.fld[i]
        logging.critical("Cannot match found field {}".format(fld_name))
        sys.exit(1)

    # TODO
    def rand_field(self, fld_name):
        pass

    # TODO
    def set_field_rand_mode(self, fld_name, rand_on):
        pass

    def reset(self):
        for i in range((len(self.fld) - 1), -1, -1):
            self.fld[i].val = self.fld[i].reset_val

    def set_val(self, val):
        for i in range((len(self.fld) - 1), -1, -1):
            if not self.fld[i].hard_wired:
                # Assign the valid msb to the field
                self.fld[i].val = (val >> (rcs.XLEN - self.fld[i].bit_width))
                logging.info("Assign field {}, bit_width:{}, reg_val 0x{},  fld_val:0x{}",
                             self.fld[i].name, self.fld[i].bit_width, val, self.fld[i].val)
            self.val = val << self.fld[i].bit_width
