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

import vsc
import random
from importlib import import_module
from pygen_src.riscv_directed_instr_lib import riscv_mem_access_stream
from pygen_src.riscv_instr_pkg import (riscv_reg_t, riscv_pseudo_instr_name_t,
                                       riscv_instr_name_t, riscv_instr_category_t,
                                       riscv_instr_group_t)
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_pseudo_instr import riscv_pseudo_instr
from pygen_src.isa.riscv_instr import riscv_instr
rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")


# Base class for AMO instruction stream
@vsc.randobj
class riscv_amo_base_instr_stream(riscv_mem_access_stream):
    def __init__(self):
        super().__init__()
        self.num_amo = vsc.rand_uint32_t()
        self.num_mixed_instr = vsc.rand_uint32_t()
        self.offset = vsc.randsz_list_t(vsc.int32_t())
        self.rs1_reg = vsc.randsz_list_t(vsc.enum_t(riscv_reg_t))
        self.num_of_rs1_reg = vsc.rand_int32_t()
        self.data_page_id = vsc.uint32_t()
        self.max_offset = vsc.uint32_t()
        self.XLEN = vsc.uint32_t(rcs.XLEN)
        # User can specify a small group of available registers to generate various hazard condition
        self.avail_regs = vsc.randsz_list_t(vsc.enum_t(riscv_reg_t))

    @vsc.constraint
    def num_of_rs1_reg_c(self):
        self.num_of_rs1_reg == 1

    @vsc.constraint
    def rs1_c(self):
        # TODO constraint size with num_of_rs1_reg
        vsc.solve_order(self.num_of_rs1_reg, self.rs1_reg)
        self.rs1_reg.size == 1  # self.num_of_rs1_reg
        self.offset.size == 1  # self.num_of_rs1_reg
        with vsc.foreach(self.rs1_reg, idx = True) as i:
            self.rs1_reg[i].not_inside(vsc.rangelist(cfg.reserved_regs,
                                                     self.reserved_rd, riscv_reg_t.ZERO))
        vsc.unique(self.rs1_reg)

    @vsc.constraint
    def addr_range_c(self):
        with vsc.foreach(self.offset, idx = True) as i:
            self.offset[i] in vsc.rangelist(vsc.rng(0, self.max_offset - 1))

    @vsc.constraint
    def aligned_amo_c(self):

        with vsc.foreach(self.offset, idx = True) as i:
            with vsc.if_then(self.XLEN == 32):
                self.offset[i] % 4 == 0
            with vsc.else_then():
                self.offset[i] % 8 == 0

    def pre_randomize(self):
        self.data_page = cfg.amo_region
        max_data_page_id = len(self.data_page)
        self.data_page_id = random.randrange(0, max_data_page_id - 1)
        self.max_offset = self.data_page[self.data_page_id]['size_in_bytes']

    # Use "la" instruction to initialize the offset regiseter
    def init_offset_reg(self):
        for i in range(len(self.rs1_reg)):
            la_instr = riscv_pseudo_instr()
            la_instr.pseudo_instr_name = riscv_pseudo_instr_name_t.LA
            la_instr.rd = self.rs1_reg[i]
            la_instr.imm_str = "{}+{}".format(cfg.amo_region[self.data_page_id]['name'],
                                              self.offset[i])
            self.instr_list.insert(0, la_instr)

    def post_randomize(self):
        self.gen_amo_instr()
        self.reserved_rd.append(self.rs1_reg)
        self.add_mixed_instr(self.num_mixed_instr)
        self.init_offset_reg()
        super().post_randomize()

    # AMO instruction generation
    def gen_amo_instr(self):
        pass


# A pair of LR/SC instruction
@vsc.randobj
class riscv_lr_sc_instr_stream (riscv_amo_base_instr_stream):
    def __init__(self):
        super().__init__()
        self.lr_instr = vsc.attr(riscv_instr())
        self.sc_instr = vsc.attr(riscv_instr())

    @vsc.constraint
    def legal_c(self):
        self.num_amo == 1
        self.num_mixed_instr in vsc.rangelist(vsc.rng(0, 15))

    def gen_amo_instr(self):
        allowed_lr_instr = []
        allowed_sc_instr = []
        if riscv_instr_group_t.RV32A in rcs.supported_isa:
            allowed_lr_instr.append(riscv_instr_name_t.LR_W)
            allowed_sc_instr.append(riscv_instr_name_t.SC_W)
        if riscv_instr_group_t.RV64A in rcs.supported_isa:
            allowed_lr_instr.append(riscv_instr_name_t.LR_D)
            allowed_sc_instr.append(riscv_instr_name_t.SC_D)
        self.lr_instr = riscv_instr.get_rand_instr(include_instr = allowed_lr_instr)
        self.sc_instr = riscv_instr.get_rand_instr(include_instr = allowed_sc_instr)
        with self.lr_instr.randomize_with():
            # self.lr_instr.rs1 == self.rs1_reg[0]  # TODO Getting error
            with vsc.if_then(self.reserved_rd.size > 0):
                self.lr_instr.rd.not_inside(vsc.rangelist(self.reserved_rd))
            with vsc.if_then(cfg.reserved_regs.size > 0):
                self.lr_instr.rd.not_inside(vsc.rangelist(cfg.reserved_regs))
            # self.lr_instr.rd != self.rs1_reg[0]  # TODO
        with self.sc_instr.randomize_with():
            # self.sc_instr.rs1 == self.rs1_reg[0]  # TODO
            with vsc.if_then(self.reserved_rd.size > 0):
                self.sc_instr.rd.not_inside(vsc.rangelist(self.reserved_rd))
            with vsc.if_then(cfg.reserved_regs.size > 0):
                self.sc_instr.rd.not_inside(vsc.rangelist(cfg.reserved_regs))
            # self.sc_instr.rd != self.rs1_reg[0]  # TODO
        self.instr_list.extend((self.lr_instr, self.sc_instr))

    '''
    section 8.3 Eventual Success of Store-Conditional Instructions
    An LR/SC sequence begins with an LR instruction and ends with an SC instruction.
    The dynamic code executed between the LR and SC instructions can only contain
    instructions from the base “I” instruction set, excluding loads, stores, backward
    jumps, taken backward branches, JALR, FENCE, and SYSTEM instructions. If the “C”
    extension is supported, then compressed forms of the aforementioned “I” instructions
    are also permitted.
    '''
    def add_mixed_instr(self, instr_cnt):
        self.setup_allowed_instr(no_branch = 1, no_load_store = 1)
        for i in range(instr_cnt):
            instr = riscv_instr()
            instr = self.randomize_instr(instr, include_group = [riscv_instr_group_t.RV32I,
                                                                 riscv_instr_group_t.RV32C])
            if instr.category not in [riscv_instr_category_t.SYSTEM, riscv_instr_category_t.SYNCH]:
                self.insert_instr(instr)


@vsc.randobj
class riscv_amo_instr_stream (riscv_amo_base_instr_stream):
    def __init__(self):
        super().__init__()
        self.amo_instr = []

    @vsc.constraint
    def reasonable_c(self):
        vsc.solve_order(self.num_amo, self.num_mixed_instr)
        self.num_amo in vsc.rangelist(vsc.rng(1, 10))
        self.num_mixed_instr in vsc.rangelist(vsc.rng(0, self.num_amo))

    @vsc.constraint
    def num_of_rs1_reg_c(self):
        vsc.solve_order(self.num_amo, self.num_of_rs1_reg)
        self.num_of_rs1_reg in vsc.rangelist(vsc.rng(1, self.num_amo))
        self.num_of_rs1_reg < 5

    def gen_amo_instr(self):
        for i in range(self.num_amo):
            self.amo_instr.append(riscv_instr.get_rand_instr(
                                  include_category=[riscv_instr_category_t.AMO]))
            with self.amo_instr[i].randomize_with():
                with vsc.if_then(self.reserved_rd.size > 0):
                    self.amo_instr[i].rd.not_inside(vsc.rangelist(self.reserved_rd))
                with vsc.if_then(cfg.reserved_regs.size > 0):
                    self.amo_instr[i].rd.not_inside(vsc.rangelist(cfg.reserved_regs))
                self.amo_instr[i].rs1.inside(vsc.rangelist(self.rs1_reg))
                self.amo_instr[i].rd.inside(vsc.rangelist(self.rs1_reg))
            self.instr_list.insert(0, self.amo_instr[i])


class riscv_vector_amo_instr_stream():
    # TODO
    pass
