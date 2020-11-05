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
import random
import logging
import vsc
from importlib import import_module
from enum import IntEnum, auto
from pygen_src.riscv_instr_stream import riscv_rand_instr_stream
from pygen_src.isa.riscv_instr import riscv_instr
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_instr_pkg import (riscv_reg_t,
                                       riscv_pseudo_instr_name_t, riscv_instr_name_t, pkg_ins)
from pygen_src.riscv_pseudo_instr import riscv_pseudo_instr
rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")


class riscv_directed_instr_stream(riscv_rand_instr_stream):

    label = ""

    def __init__(self):
        super().__init__()
        self.name = ""

    def post_randomize(self):
        for i in range(len(self.instr_list)):
            self.instr_list[i].has_label = 0
            self.instr_list[i].atomic = 1
        self.instr_list[0].comment = "Start %0s" % (self.name)
        self.instr_list[-1].comment = "End %0s" % (self.name)
        if riscv_directed_instr_stream.label != "":
            self.instr_list[0].label = riscv_directed_instr_stream.label
            self.instr_list[0].has_label = 1


@vsc.randobj
class riscv_jal_instr(riscv_rand_instr_stream):
    def __init__(self):
        super().__init__()
        self.name = ""
        self.jump = []
        self.jump_start = riscv_instr()
        self.jump_end = riscv_instr()
        self.num_of_jump_instr = vsc.rand_int_t()

    @vsc.constraint
    def instr_c(self):
        self.num_of_jump_instr in vsc.rangelist(vsc.rng(10, 30))

    def post_randomize(self):
        order = []
        RA = cfg.ra
        order = [0] * self.num_of_jump_instr
        self.jump = [0] * self.num_of_jump_instr
        for i in range(len(order)):
            order[i] = i
        random.shuffle(order)
        self.setup_allowed_instr(1, 1)
        jal = [riscv_instr_name_t.JAL]
        if not cfg.disable_compressed_instr:
            jal.append(riscv_instr_name_t.C_J)
            if rcs.XLEN == 32:
                jal.append(riscv_instr_name_t.C_JAL)
        self.jump_start = riscv_instr.get_instr(riscv_instr_name_t.JAL.name)
        with self.jump_start.randomize_with() as it:
            self.jump_start.rd == RA
        self.jump_start.imm_str = "{}f".format(order[0])
        self.jump_start.label = self.label

        # Last instruction
        self.jump_end = self.randomize_instr(self.jump_end)
        self.jump_end.label = "{}".format(self.num_of_jump_instr)
        for i in range(self.num_of_jump_instr):
            self.jump[i] = riscv_instr.get_rand_instr(include_instr = [jal[0].name])
            with self.jump[i].randomize_with() as it:
                if self.jump[i].has_rd:
                    vsc.dist(self.jump[i].rd, [vsc.weight(riscv_reg_t.RA, 5), vsc.weight(
                        vsc.rng(riscv_reg_t.SP, riscv_reg_t.T0), 1),
                        vsc.weight(vsc.rng(riscv_reg_t.T2, riscv_reg_t.T6), 2)])
                    self.jump[i].rd.not_inside(cfg.reserved_regs)
            self.jump[i].label = "{}".format(i)

        for i in range(len(order)):
            if i == self.num_of_jump_instr - 1:
                self.jump[order[i]].imm_str = "{}f".format(self.num_of_jump_instr)
            else:
                if order[i + 1] > order[i]:
                    self.jump[order[i]].imm_str = "{}f".format(order[i + 1])
                else:
                    self.jump[order[i]].imm_str = "{}b".format(order[i + 1])
        self.instr_list.append(self.jump_start)
        self.instr_list.extend(self.jump)
        self.instr_list.append(self.jump_end)
        for i in range(len(self.instr_list)):
            self.instr_list[i].has_label = 1
            self.instr_list[i].atomic = 1


class int_numeric_e(IntEnum):
    NormalValue = auto()
    Zero = auto()
    AllOne = auto()
    NegativeMax = auto()


@vsc.randobj
class riscv_int_numeric_corner_stream(riscv_directed_instr_stream):
    def __init__(self):
        super().__init__()
        self.num_of_avail_regs = 10
        self.num_of_instr = vsc.rand_uint8_t()
        self.init_val = vsc.rand_list_t(vsc.rand_bit_t(rcs.XLEN - 1), sz = 10)
        self.init_val_type = vsc.rand_list_t(vsc.enum_t(int_numeric_e), sz =10)
        self.init_instr = []

    @vsc.constraint
    def init_val_c(self):
        # TO DO
        # solve init_val_type before init_val;
        self.init_val_type.size == self.num_of_avail_regs
        self.init_val.size == self.num_of_avail_regs
        self.num_of_instr in vsc.rangelist(vsc.rng(15, 30))

    @vsc.constraint
    def avail_regs_c(self):
        self.avail_regs.size == self.num_of_avail_regs
        vsc.unique(self.avail_regs)
        with vsc.foreach(self.avail_regs, idx = True) as i:
            self.avail_regs[i].not_inside(cfg.reserved_regs)
            self.avail_regs[i] != riscv_reg_t.ZERO

    def pre_randomize(self):
        pass

    def post_randomize(self):
        self.init_instr = [None] * self.num_of_avail_regs
        for i in range(len(self.init_val_type)):
            if self.init_val_type[i] == int_numeric_e.Zero:
                self.init_val[i] = 0
            elif self.init_val_type[i] == int_numeric_e.AllOne:
                self.init_val[i] = 1
            elif self.init_val_type[i] == int_numeric_e.NegativeMax:
                self.init_val[i] = 1 << (rcs.XLEN - 1)
            self.init_instr[i] = riscv_pseudo_instr()
            self.init_instr[i].rd = self.avail_regs[i]
            self.init_instr[i].pseudo_instr_name = riscv_pseudo_instr_name_t.LI
            self.init_instr[i].imm_str = "0x%0x" % (self.init_val[i])
            self.instr_list.append(self.init_instr[i])
        for i in range(self.num_of_instr):
            instr = riscv_instr.get_rand_instr(
                include_category = ['ARITHMETIC'],
                exclude_group = ['RV32C', 'RV64C', 'RV32F', 'RV64F', 'RV32D', 'RV64D'])
            instr = self.randomize_gpr(instr)
            self.instr_list.append(instr)
        super().post_randomize()


# Push Stack Instructions
class riscv_push_stack_instr(riscv_rand_instr_stream):

    def __init__(self):
        super().__init__()
        self.stack_len = 0
        self.num_of_reg_to_save = 0
        self.num_of_redundant_instr = 0
        self.push_stack_instr = []
        self.saved_regs = []
        self.branch_instr = riscv_instr()
        self.enable_branch = vsc.rand_bit_t()
        self.push_start_label = ''

    def init(self):
        self.reserved_rd = [cfg.ra]
        self.saved_regs = [cfg.ra]
        self.num_of_reg_to_save = len(self.saved_regs)
        if self.num_of_reg_to_save * (rcs.XLEN / 8) > self.stack_len:
            logging.error('stack len [%0d] is not enough to store %d regs',
                          self.stack_len, self.num_of_reg_to_save)
            sys.exit(1)
        self.num_of_redundant_instr = random.randrange(3, 10)
        self.initialize_instr_list(self.num_of_redundant_instr)

    def gen_push_stack_instr(self, stack_len, allow_branch=1):
        self.stack_len = stack_len
        self.init()
        self.push_stack_instr = [0] * (self.num_of_reg_to_save + 1)
        for i in range(len(self.push_stack_instr)):
            self.push_stack_instr[i] = riscv_instr()
        self.push_stack_instr[0] = \
            riscv_instr.get_instr(riscv_instr_name_t.ADDI.name)
        with self.push_stack_instr[0].randomize_with() as it:
            self.push_stack_instr[0].rd == cfg.sp
            self.push_stack_instr[0].rs1 == cfg.sp
            self.push_stack_instr[0].imm == (~cfg.stack_len) + 1

        self.push_stack_instr[0].imm_str = '-{}'.format(self.stack_len)
        for i in range(len(self.saved_regs)):
            if rcs.XLEN == 32:
                self.push_stack_instr[i + 1] = riscv_instr.get_instr(riscv_instr_name_t.SW.name)
                with self.push_stack_instr[i + 1].randomize_with() as it:
                    self.push_stack_instr[i + 1].rs2 == self.saved_regs[i]
                    self.push_stack_instr[i + 1].rs1 == cfg.sp
                    self.push_stack_instr[i + 1].imm == 4 * (i + 1)
            else:
                self.push_stack_instr[i + 1] = riscv_instr.get_instr(riscv_instr_name_t.SD.name)
                with self.push_stack_instr[i + 1].randomize_with() as it:
                    self.push_stack_instr[i + 1].rs2 == self.saved_regs[i]
                    self.push_stack_instr[i + 1].rs1 == cfg.sp
                    self.push_stack_instr[i + 1].imm == 8 * (i + 1)

            self.push_stack_instr[i + 1].process_load_store = 0
        if allow_branch:
            # TODO `DV_CHECK_STD_RANDOMIZE_FATAL(enable_branch)
            pass
        else:
            self.enable_branch = 0
        if self.enable_branch:
            self.branch_instr = \
                riscv_instr.get_rand_instr(include_category=[riscv_instr_name_t.BRANCH.name])
            # `DV_CHECK_STD_RANDOMIZE_FATAL(branch_instr)
            self.branch_instr.imm_str = self.push_start_label
            self.branch_instr.brach_assigned = 1
            self.push_stack_instr[0].label = self.push_start_label
            self.push_stack_instr[0].has_label = 1
            self.branch_instr.extend(self.push_stack_instr)
        self.mix_instr_stream(self.push_stack_instr)
        for i in range(len(self.instr_list)):
            self.instr_list[i].atomic = 1
            if self.instr_list[i].label == '':
                self.instr_list[i].has_label = 0


# Pop stack instruction stream
class riscv_pop_stack_instr(riscv_rand_instr_stream):

    def __init__(self):
        super().__init__()
        self.stack_len = 0
        self.num_of_reg_to_save = 0
        self.num_of_redundant_instr = 0
        self.pop_stack_instr = []
        self.saved_regs = []

    def init(self):
        self.reserved_rd = [cfg.ra]
        self.num_of_reg_to_save = len(self.saved_regs)
        if self.num_of_reg_to_save * 4 > self.stack_len:
            logging.error('stack len [%0d] is not enough to store %d regs',
                          self.stack_len, self.num_of_reg_to_save)
            sys.exit(1)
        self.num_of_redundant_instr = random.randrange(3, 10)
        self.initialize_instr_list(self.num_of_redundant_instr)

    def gen_pop_stack_instr(self, stack_len, saved_regs):
        self.stack_len = stack_len
        self.saved_regs = saved_regs
        self.init()
        self.gen_instr(1)
        self.pop_stack_instr = [None] * (self.num_of_reg_to_save + 1)
        for i in range(len(self.pop_stack_instr)):
            self.pop_stack_instr[i] = riscv_instr()
        for i in range(len(self.saved_regs)):
            if rcs.XLEN == 32:
                self.pop_stack_instr[i] = riscv_instr.get_instr(riscv_instr_name_t.LW.name)
                with self.pop_stack_instr[i].randomize_with() as it:
                    self.rd == self.saved_regs[i]
                    self.rs1 == cfg.sp
                    self.imm == 4 * (i + 1)
            else:
                self.pop_stack_instr[i] = riscv_instr.get_instr(riscv_instr_name_t.LD.name)
                with self.pop_stack_instr[i].randomize_with() as it:
                    self.rd == self.saved_regs[i]
                    self.rs1 == cfg.sp
                    self.imm == 8 * (i + 1)
            self.pop_stack_instr[i].process_load_store = 0
        # addi sp,sp,imm
        ''' TODO `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[num_of_reg_to_save],
                                   rd == cfg.sp; rs1 == cfg.sp; imm == stack_len;) '''
        self.pop_stack_instr[self.num_of_reg_to_save] = riscv_instr.get_instr(
            riscv_instr_name_t.ADDI.name)
        self.pop_stack_instr[self.num_of_reg_to_save].imm_str = pkg_ins.format_string(
            '{}', self.stack_len)
        self.mix_instr_stream(self.pop_stack_instr)
        for i in range(len(self.instr_list)):
            self.instr_list[i].atomic = 1
            self.instr_list[i].has_label = 0
