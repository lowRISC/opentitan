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
import sys
import logging
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.isa.riscv_instr import riscv_instr
from pygen_src.riscv_instr_stream import riscv_rand_instr_stream
from pygen_src.riscv_instr_pkg import (riscv_reg_t, riscv_instr_name_t, pkg_ins,
                                       riscv_instr_format_t, riscv_instr_category_t,
                                       compressed_gpr)


@vsc.randobj
class riscv_loop_instr(riscv_rand_instr_stream):

    def __init__(self):
        super().__init__()
        self.loop_cnt_reg = vsc.randsz_list_t(vsc.enum_t(riscv_reg_t))
        self.loop_limit_reg = vsc.randsz_list_t(vsc.enum_t(riscv_reg_t))
        self.loop_init_val = vsc.randsz_list_t(vsc.int32_t())
        self.loop_step_val = vsc.randsz_list_t(vsc.int32_t())
        self.loop_limit_val = vsc.randsz_list_t(vsc.int32_t())
        self.num_of_nested_loop = vsc.rand_bit_t(3)
        self.num_of_instr_in_loop = vsc.rand_int32_t(0)
        self.branch_type = vsc.randsz_list_t(vsc.enum_t(riscv_instr_name_t))
        self.loop_init_instr = []
        self.loop_update_instr = []
        self.loop_branch_instr = []
        self.loop_branch_target_instr = []
        # Aggregated loop instruction stream
        self.loop_instr = []

    @vsc.constraint
    def legal_loop_regs_c(self):
        self.num_of_nested_loop.inside(vsc.rangelist(1, 2))
        self.loop_limit_reg.size.inside(vsc.rangelist((1, 32)))
        self.loop_cnt_reg.size.inside(vsc.rangelist((1, 8)))
        vsc.solve_order(self.num_of_nested_loop, self.loop_cnt_reg)
        vsc.solve_order(self.num_of_nested_loop, self.loop_limit_reg)
        with vsc.foreach(self.loop_cnt_reg, idx = True) as i:
            self.loop_cnt_reg[i] != riscv_reg_t.ZERO
            with vsc.foreach(cfg.reserved_regs, idx = True) as j:
                self.loop_cnt_reg[i] != cfg.reserved_regs[j]
        with vsc.foreach(self.loop_limit_reg, idx = True) as i:
            with vsc.foreach(cfg.reserved_regs, idx = True) as j:
                self.loop_limit_reg[i] != cfg.reserved_regs[j]
        vsc.unique(self.loop_cnt_reg)
        vsc.unique(self.loop_limit_reg)
        self.loop_cnt_reg.size == self.num_of_nested_loop
        self.loop_limit_reg.size == self.num_of_nested_loop

    @vsc.constraint
    def loop_c(self):
        vsc.solve_order(self.num_of_nested_loop, self.loop_init_val)
        vsc.solve_order(self.num_of_nested_loop, self.loop_step_val)
        vsc.solve_order(self.num_of_nested_loop, self.loop_limit_val)
        vsc.solve_order(self.loop_limit_val, self.loop_limit_reg)
        vsc.solve_order(self.branch_type, self.loop_init_val)
        vsc.solve_order(self.branch_type, self.loop_step_val)
        vsc.solve_order(self.branch_type, self.loop_limit_val)
        self.num_of_instr_in_loop.inside(vsc.rangelist((1, 25)))
        self.num_of_nested_loop.inside(vsc.rangelist(1, 2))
        self.loop_init_val.size.inside(vsc.rangelist(1, 2))
        self.loop_step_val.size.inside(vsc.rangelist(1, 2))
        self.loop_limit_val.size.inside(vsc.rangelist(1, 2))
        self.branch_type.size.inside(vsc.rangelist(1, 2))
        self.loop_init_val.size == self.num_of_nested_loop
        self.branch_type.size == self.num_of_nested_loop
        self.loop_step_val.size == self.num_of_nested_loop
        self.loop_limit_val.size == self.num_of_nested_loop
        self.branch_type.size == self.num_of_nested_loop
        with vsc.foreach(self.branch_type, idx = True) as i:
            with vsc.if_then(cfg.disable_compressed_instr == 0):
                self.branch_type[i].inside(vsc.rangelist(riscv_instr_name_t.C_BNEZ,
                                                         riscv_instr_name_t.C_BEQZ,
                                                         riscv_instr_name_t.BEQ,
                                                         riscv_instr_name_t.BNE,
                                                         riscv_instr_name_t.BLTU,
                                                         riscv_instr_name_t.BLT,
                                                         riscv_instr_name_t.BGEU,
                                                         riscv_instr_name_t.BGE))
            with vsc.else_then():
                self.branch_type[i].inside(vsc.rangelist(riscv_instr_name_t.BEQ,
                                                         riscv_instr_name_t.BNE,
                                                         riscv_instr_name_t.BLTU,
                                                         riscv_instr_name_t.BLT,
                                                         riscv_instr_name_t.BGEU,
                                                         riscv_instr_name_t.BGE))
        with vsc.foreach(self.loop_init_val, idx = True) as i:
            with vsc.if_then(self.branch_type[i].inside(vsc.rangelist(riscv_instr_name_t.C_BNEZ,
                                                                      riscv_instr_name_t.C_BEQZ))):
                self.loop_limit_val[i] == 0
                self.loop_limit_reg[i] == riscv_reg_t.ZERO
                self.loop_cnt_reg[i].inside(vsc.rangelist(list(compressed_gpr)))
            with vsc.else_then:
                self.loop_limit_val[i].inside(vsc.rangelist((-20, 20)))
                self.loop_limit_reg[i] != riscv_reg_t.ZERO
            with vsc.if_then(self.branch_type[i].inside(vsc.rangelist(riscv_instr_name_t.C_BNEZ,
                                                                      riscv_instr_name_t.C_BEQZ,
                                                                      riscv_instr_name_t.BEQ,
                                                                      riscv_instr_name_t.BNE))):
                self.loop_limit_val[i] != self.loop_init_val[i]
                ((self.loop_limit_val[i] - self.loop_init_val[i]) % self.loop_step_val[i]) == 0
            with vsc.else_if(self.branch_type[i] == riscv_instr_name_t.BGE):
                self.loop_step_val[i] < 0
            with vsc.else_if(self.branch_type[i].inside(vsc.rangelist(riscv_instr_name_t.BGEU))):
                self.loop_step_val[i] < 0
                self.loop_init_val[i] > 0
                # Avoid count to negative
                (self.loop_step_val[i] + self.loop_limit_val[i]) > 0
            with vsc.else_if(self.branch_type[i] == riscv_instr_name_t.BLT):
                self.loop_step_val[i] > 0
            with vsc.else_if(self.branch_type[i] == riscv_instr_name_t.BLTU):
                self.loop_step_val[i] > 0
                self.loop_limit_val[i] > 0
            self.loop_init_val[i].inside(vsc.rangelist((-10, 10)))
            self.loop_step_val[i].inside(vsc.rangelist((-10, 10)))
            with vsc.if_then(self.loop_init_val[i] < self.loop_limit_val[i]):
                self.loop_step_val[i] > 0
            with vsc.else_then:
                self.loop_step_val[i] < 0

    def post_randomize(self):
        for i in range(len(self.loop_cnt_reg)):
            self.reserved_rd.append(self.loop_cnt_reg[i])
        for i in range(len(self.loop_limit_reg)):
            self.reserved_rd.append(self.loop_limit_reg[i])
        # Generate instructions that mixed with the loop instructions
        self.initialize_instr_list(self.num_of_instr_in_loop)
        self.gen_instr(1)
        # Randomize the key loop instructions
        self.loop_init_instr = [0] * 2 * self.num_of_nested_loop
        self.loop_update_instr = [0] * self.num_of_nested_loop
        self.loop_branch_instr = [0] * self.num_of_nested_loop
        self.loop_branch_target_instr = [0] * self.num_of_nested_loop
        for i in range(self.num_of_nested_loop):
            # Instruction to init the loop counter
            try:
                self.loop_init_instr.insert(2 * i, riscv_instr.get_rand_instr())
                # TODO
                '''self.loop_update_instr[i] = riscv_instr.get_rand_instr(
                include_instr = [riscv_instr_name_t.ADDI])'''
                # Removed include_instr ADDI for now to avoid unrecognized colon
                with self.loop_init_instr[2 * i].randomize_with():
                    self.loop_init_instr[2 * i].rd == self.loop_cnt_reg[i]
                    self.loop_init_instr[2 * i].rs1 == riscv_reg_t.ZERO
                    self.loop_init_instr[2 * i].imm == self.loop_init_val[i]
                    self.loop_init_instr[2 * i].comment = \
                        pkg_ins.format_string("init loop {} counter".format(i))
            except Exception:
                logging.critical("Cannot randomize loop init1 instruction")
                sys.exit(1)
            # Instruction to init loop limit
            try:
                self.loop_init_instr[2 * i + 1] = riscv_instr.get_rand_instr()
                # TODO
                '''self.loop_update_instr[i] = riscv_instr.get_rand_instr(
                include_instr = [riscv_instr_name_t.ADDI])'''
                # Removed include_instr ADDI for now to avoid unrecognized colon
                with self.loop_init_instr[2 * i + 1].randomize_with():
                    self.loop_init_instr[2 * i + 1].rd == self.loop_limit_reg[i]
                    self.loop_init_instr[2 * i + 1].rs1 == riscv_reg_t.ZERO
                    self.loop_init_instr[2 * i + 1].imm == self.loop_limit_val[i]
                    self.loop_init_instr[2 * i + 1].comment = \
                        pkg_ins.format_string("init loop {} limit".format(i))
            except Exception:
                logging.critical("Cannot randomize loop init2 instruction")
                sys.exit(1)
            # Branch target instruction, can be anything
            self.loop_branch_target_instr[i] = riscv_instr.get_rand_instr(
                include_category = [riscv_instr_category_t.ARITHMETIC.name,
                                    riscv_instr_category_t.LOGICAL.name,
                                    riscv_instr_category_t.COMPARE.name],
                exclude_instr = [riscv_instr_name_t.C_ADDI16SP])
            try:
                with self.loop_branch_target_instr[i].randomize_with():
                    with vsc.if_then(self.loop_branch_target_instr[i].format ==
                                     riscv_instr_format_t.CB_FORMAT):
                        self.loop_branch_target_instr[i].rs1.not_inside(
                            vsc.rangelist(self.reserved_rd))
                        self.loop_branch_target_instr[i].rs1.not_inside(
                            vsc.rangelist(cfg.reserved_regs))
                    with vsc.if_then(self.loop_branch_target_instr[i].has_rd == 1):
                        self.loop_branch_target_instr[i].rd.not_inside(
                            vsc.rangelist(self.reserved_rd))
                        self.loop_branch_target_instr[i].rd.not_inside(
                            vsc.rangelist(cfg.reserved_regs))
            except Exception:
                logging.critical("Cannot randomize branch target instruction")
                sys.exit(1)
            self.loop_branch_target_instr[i].label = pkg_ins.format_string(
                "{}_{}_t".format(self.label, i))
            # Instruction to update loop counter
            self.loop_update_instr[i] = riscv_instr.get_rand_instr()
            # TODO
            '''self.loop_update_instr[i] = riscv_instr.get_rand_instr(
                include_instr = [riscv_instr_name_t.ADDI])'''
            # Removing include_instr ADDI for now to avoid unrecognized colon
            # Commenting for now due to key error
            '''with self.loop_update_instr[i].randomize_with():
                self.loop_update_instr[i].rd == self.loop_cnt_reg[i]
                self.loop_update_instr[i].rs1 == self.loop_cnt_reg[i]
                self.loop_update_instr[i].imm == self.loop_step_val[i]'''
            self.loop_update_instr[i].comment = pkg_ins.format_string(
                "update loop {} counter".format(i))
            # Backward branch instruction
            self.loop_branch_instr[i] = riscv_instr.get_rand_instr(
                include_instr = [self.branch_type[i]])
            self.loop_branch_instr[i].randomize()
            with self.loop_branch_instr[i].randomize_with():
                self.loop_branch_instr[i].rs1 == self.loop_cnt_reg[i]
                # Getting PyVSC related error
                # TODO
                '''with vsc.if_then((self.branch_type[i] != riscv_instr_name_t.C_BEQZ) or
                                 (self.branch_type[i] != riscv_instr_name_t.C_BNEZ)):
                    self.loop_branch_instr[i].rs2 == self.loop_limit_reg[i]
                '''
            self.loop_branch_instr[i].comment = pkg_ins.format_string(
                "branch for loop {}".format(i))
            self.loop_branch_instr[i].imm_str = self.loop_branch_target_instr[i].label
            self.loop_branch_instr[i].branch_assigned = 1
        # Randomly distribute the loop instruction in the existing instruction stream
        self.build_loop_instr_stream()
        self.mix_instr_stream(self.loop_instr, 1)
        for i in range(len(self.instr_list)):
            if (self.instr_list[i].label != ""):
                self.instr_list[i].has_label = 1
            else:
                self.instr_list[i].has_label = 0
            self.instr_list[i].atomic = 1

    # Build the whole loop structure from innermost loop to the outermost loop
    def build_loop_instr_stream(self):
        self.loop_instr = []
        for i in range(self.num_of_nested_loop):
            self.loop_instr.append(self.loop_init_instr[2 * i])
            self.loop_instr.append(self.loop_init_instr[2 * i + 1])
            self.loop_instr.append(self.loop_branch_target_instr[i])
            self.loop_instr.append(self.loop_update_instr[i])
            self.loop_instr.append(self.loop_instr[i])
            self.loop_instr.append(self.loop_branch_instr[i])
        logging.info("Totally {} instructions have been added".format(len(self.loop_instr)))
