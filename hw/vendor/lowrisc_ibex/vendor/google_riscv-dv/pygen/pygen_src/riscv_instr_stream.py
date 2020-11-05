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
import random
import logging
import sys
import vsc
from pygen_src.riscv_instr_pkg import riscv_instr_name_t,\
    riscv_instr_category_t, riscv_instr_format_t, riscv_reg_t
from pygen_src.isa.riscv_instr import riscv_instr
from pygen_src.riscv_instr_gen_config import cfg


@vsc.randobj
class riscv_instr_stream:
    '''
     Base class for RISC-V instruction stream
     A instruction stream here is a queue of RISC-V basic instructions.
     This class also provides some functions to manipulate the instruction stream, like insert a new
     instruction, mix two instruction streams etc.
    '''

    def __init__(self):
        self.instr_list = []
        self.instr_cnt = 0
        self.label = ""
        # User can specify a small group of available registers to generate various hazard condition
        self.avail_regs = vsc.rand_list_t(vsc.enum_t(riscv_reg_t), sz = 10)
        # Some additional reserved registers that should not be used as rd register
        # by this instruction stream
        self.reserved_rd = vsc.list_t(vsc.enum_t(riscv_reg_t))
        self.hart = 0

    def initialize_instr_list(self, instr_cnt):
        self.instr_list.clear()
        self.instr_cnt = instr_cnt
        self.create_instr_instance()

    def create_instr_instance(self):
        for i in range(self.instr_cnt):
            instr = riscv_instr()
            self.instr_list.append(instr)

    def insert_instr(self, instr, idx = -1):
        """
           Insert an instruction to the existing instruction stream at the given index
           When index is -1, the instruction is injected at a random location
        """
        current_instr_cnt = len(self.instr_list)
        if idx == -1:
            idx = random.randint(0, current_instr_cnt - 1)
            while self.instr_list[idx].atomic:
                idx = idx + 1
                if idx == (current_instr_cnt - 1):
                    self.instr_list.append(instr)
                    return
        elif idx > current_instr_cnt or idx < 0:
            logging.error("Cannot insert instr:%0s at idx %0d", instr.convert2asm(), idx)
            sys.exit(1)
        self.instr_list.insert(idx, instr)

    def insert_instr_stream(self, new_instr, idx = -1, replace = 0):
        """
            Insert an instruction to the existing instruction stream at the given index
            When index is -1, the instruction is injected at a random location
            When replace is 1, the original instruction at the inserted position will be replaced
        """
        current_instr_cnt = len(self.instr_list)

        if current_instr_cnt == 0:
            self.instr_list = new_instr
            return

        if idx == -1:
            idx = random.randint(0, current_instr_cnt - 1)
            # cares must be taken to avoid targeting
            # an atomic instruction (while atomic, find a new idx)
            for i in range(10):
                if self.instr_list[idx].atomic:
                    break
                idx = random.randint(0, current_instr_cnt - 1)
            if self.instr_list[idx].atomic:
                for i in range(len(self.instr_list)):
                    if not self.instr_list[i].atomic:
                        idx = i
                        break
                if self.instr_list[idx].atomic:
                    logging.critical("Cannot inject the instruction")
                    sys.exit(1)
        elif idx > current_instr_cnt or idx < 0:
            logging.error("Cannot insert instr stream at idx %0d", idx)
            sys.exit(1)
        # When replace is 1, the original instruction at this index will be removed.
        # The label of the original instruction will be copied to the head
        # of inserted instruction stream.
        if replace:
            new_instr[0].label = self.instr_list[idx].label
            new_instr[0].has_label = self.instr_list[idx].has_label
            if idx == 0:
                self.instr_list = new_instr + self.instr_list[idx + 1:current_instr_cnt]
            else:
                self.instr_list = self.instr_list[0:idx] + new_instr + \
                    self.instr_list[idx + 1:current_instr_cnt]
        else:
            if idx == 0:
                self.instr_list = new_instr + self.instr_list[idx:current_instr_cnt]
            else:
                self.instr_list = self.instr_list[0:idx] + new_instr + \
                    self.instr_list[idx:current_instr_cnt]

    def mix_instr_stream(self, new_instr, contained = 0):
        """
        Mix the input instruction stream with the original instruction, the instruction order is
        preserved. When 'contained' is set, the original instruction stream will be inside the
        new instruction stream with the first and last instruction from the input instruction
        stream.
        new_instr is a list of riscv_instr
        """
        current_instr_cnt = len(self.instr_list)
        new_instr_cnt = len(new_instr)
        insert_instr_position = [0] * new_instr_cnt
        if len(insert_instr_position) > 0:
            insert_instr_position.sort()
        for i in range(new_instr_cnt):
            insert_instr_position[i] = random.randint(0, current_instr_cnt)
        if len(insert_instr_position) > 0:
            insert_instr_position.sort()
        if contained:
            insert_instr_position[0] = 0
            if new_instr_cnt > 1:
                insert_instr_position[new_instr_cnt - 1] = current_instr_cnt - 1
        for i in range(len(new_instr)):
            self.insert_instr(new_instr[i], insert_instr_position[i] + i)

    def convert2string(self):
        s = ""
        for i in range(len(self.instr_list)):
            s = s + self.instr_list[i].convert2asm() + "\n"
        return s


class riscv_rand_instr_stream(riscv_instr_stream):
    """
    Generate a random instruction stream based on the configuration
    There are two ways to use this class to generate instruction stream
        1. For short instruction stream, you can call randomize() directly.
        2. For long instruction stream (>1K), randomize() all instructions together might take a
           long time for the constraint solver. In this case, you can call gen_instr to generate
           instructions one by one. The time only grows linearly with the instruction count
    """

    def __init__(self):
        # calling super constructor
        super().__init__()
        self.kernel_mode = 0
        self.allowed_instr = []
        self.category_dist = []

    def create_instr_instance(self):
        for i in range(self.instr_cnt):
            self.instr_list.append(None)

    def setup_allowed_instr(self, no_branch = 0, no_load_store = 1):
        self.allowed_instr = riscv_instr.basic_instr
        if no_branch == 0:
            self.allowed_instr.extend(
                riscv_instr.instr_category[riscv_instr_category_t.BRANCH.name])
        if no_load_store == 0:
            self.allowed_instr.extend(
                riscv_instr.instr_category[riscv_instr_category_t.LOAD.name])
            self.allowed_instr.extend(
                riscv_instr.instr_category[riscv_instr_category_t.STORE.name])
        self.setup_instruction_dist(no_branch, no_load_store)

    # TODO
    def randomize_avail_regs(self):
        pass

    def setup_instruction_dist(self, no_branch = 0, no_load_store = 1):
        if cfg.dist_control_mode:
            self.category_dist = cfg.category_dist
            if no_branch:
                self.category_dist[riscv_instr_category_t.BRANCH.name] = 0
            if no_load_store:
                self.category_dist[riscv_instr_category_t.LOAD.name] = 0
                self.category_dist[riscv_instr_category_t.STORE.name] = 0
            logging.info("setup_instruction_dist: %0d", len(self.category_dist))

    def gen_instr(self, no_branch = 0, no_load_store = 1, is_debug_program = 0):
        self.setup_allowed_instr(no_branch, no_load_store)
        for i in range(len(self.instr_list)):
            self.instr_list[i] = self.randomize_instr(self.instr_list[i], is_debug_program)
        while self.instr_list[-1].category == riscv_instr_category_t.BRANCH:
            self.instr_list.pop()
            if len(self.instr_list) == 0:
                break

    def randomize_instr(self, instr, is_in_debug = 0):
        exclude_instr = []
        is_SP_in_reserved_rd = riscv_reg_t.SP in self.reserved_rd
        is_SP_in_reserved_regs = riscv_reg_t.SP in cfg.reserved_regs
        is_SP_in_avail_regs = riscv_reg_t.SP in self.avail_regs
        if ((is_SP_in_reserved_rd or is_SP_in_reserved_regs) or
                (len(self.avail_regs) > 0 and not is_SP_in_avail_regs)):
            exclude_instr.append(riscv_instr_name_t.C_ADDI4SPN.name)
            exclude_instr.append(riscv_instr_name_t.C_ADDI16SP.name)
            exclude_instr.append(riscv_instr_name_t.C_LWSP.name)
            exclude_instr.append(riscv_instr_name_t.C_LDSP.name)
        # Post-process the allowed_instr and exclude_instr lists to handle
        # adding ebreak instructions into the debug ROM.
        if is_in_debug:
            if (cfg.no_ebreak and cfg.enable_ebreak_in_debug_rom):
                self.allowed_instr.extend([riscv_instr_name_t.EBREAK.name,
                                           riscv_instr_name_t.C_EBREAK.name])
            elif (not cfg.no_ebreak and not cfg.enable_ebreak_in_debug_rom):
                exclude_instr.extend([riscv_instr_name_t.EBREAK.name,
                                      riscv_instr_name_t.C_EBREAK.name])
        instr = riscv_instr.get_rand_instr(
            include_instr = self.allowed_instr, exclude_instr = exclude_instr)
        instr = self.randomize_gpr(instr)
        return instr

    def randomize_gpr(self, instr):
        with instr.randomize_with() as it:
            if self.avail_regs.size > 0:
                if instr.has_rs1:
                    instr.rs1.inside(vsc.rangelist(self.avail_regs))
                if instr.has_rs2:
                    instr.rs2.inside(vsc.rangelist(self.avail_regs))
                if instr.has_rd:
                    instr.rd.inside(vsc.rangelist(self.avail_regs))
            with vsc.foreach(self.reserved_rd, idx = True) as i:
                if instr.has_rd == 1:
                    instr.rd != self.reserved_rd[i]
                if instr.format == riscv_instr_format_t.CB_FORMAT:
                    instr.rs1 != self.reserved_rd[i]

            with vsc.foreach(cfg.reserved_regs, idx = True) as i:
                with vsc.if_then(instr.has_rd == 1):
                    instr.rd != cfg.reserved_regs[i]
                with vsc.if_then(instr.format == riscv_instr_format_t.CB_FORMAT):
                    instr.rs1 != cfg.reserved_regs[i]
        # TODO: Add constraint for CSR, floating point register
        return instr
