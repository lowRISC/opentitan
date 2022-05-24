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

import logging
import vsc
from pygen_src.isa.riscv_instr import riscv_instr
from pygen_src.isa.riscv_cov_instr import riscv_cov_instr, operand_sign_e
from pygen_src.riscv_instr_pkg import (pkg_ins, riscv_fpr_t, riscv_instr_format_t,
                                       riscv_instr_category_t, get_val)


@vsc.randobj
class riscv_floating_point_instr(riscv_instr):
    def __init__(self):
        super().__init__()
        self.fs1 = vsc.rand_enum_t(riscv_fpr_t)
        self.fs2 = vsc.rand_enum_t(riscv_fpr_t)
        self.fs3 = vsc.rand_enum_t(riscv_fpr_t)
        self.fd = vsc.rand_enum_t(riscv_fpr_t)
        self.has_fs1 = vsc.bit_t(1, 1)
        self.has_fs2 = vsc.bit_t(1, 1)
        self.has_fs3 = vsc.bit_t(1)
        self.has_fd = vsc.bit_t(1, 1)
        self.riscv_cov_ins = None

    def convert2asm(self, prefix = " "):
        asm_str = pkg_ins.format_string(string = self.get_instr_name(),
                                        length = pkg_ins.MAX_INSTR_STR_LEN)
        if self.format == riscv_instr_format_t.I_FORMAT:
            if self.category == riscv_instr_category_t.LOAD:
                asm_str = "{}{}, {}({})".format(asm_str, self.fd.name,
                                                self.get_imm(), self.rs1.name)
            elif self.instr_name.name in ['FMV_X_W', 'FMV_X_D', 'FCVT_W_S', 'FCVT_WU_S',
                                          'FCVT_L_S', 'FCVT_LU_S', 'FCVT_L_D', 'FCVT_LU_D',
                                          'FCVT_W_D', 'FCVT_WU_D']:
                asm_str = "{}{}, {}".format(asm_str, self.rd.name, self.fs1.name)
            elif self.instr_name.name in ['FMV_W_X', 'FMV_D_X', 'FCVT_S_W', 'FCVT_S_WU',
                                          'FCVT_S_L', 'FCVT_D_L', 'FCVT_S_LU', 'FCVT_D_W',
                                          'FCVT_D_LU', 'FCVT_D_WU']:
                asm_str = "{}{}, {}".format(asm_str, self.fd.name, self.rs1.name)
            else:
                asm_str = "{}{}, {}".format(asm_str, self.fd.name, self.fs1.name)
        elif self.format == riscv_instr_format_t.S_FORMAT:
            asm_str = "{}{}, {}({})".format(asm_str, self.fs2.name, self.get_imm(), self.rs1.name)
        elif self.format == riscv_instr_format_t.R_FORMAT:
            if self.category == riscv_instr_category_t.COMPARE:
                asm_str = "{}{}, {}, {}".format(asm_str, self.rd.name, self.fs1.name, self.fs2.name)
            elif self.instr_name.name in ['FCLASS_S', 'FCLASS_D']:
                asm_str = "{}{}, {}".format(asm_str, self.rd.name, self.fs1.name)
            else:
                asm_str = "{}{}, {}, {}".format(asm_str, self.fd.name, self.fs1.name, self.fs2.name)
        elif self.format == riscv_instr_format_t.R4_FORMAT:
            asm_str = "{}{}, {}, {}, {}".format(
                asm_str, self.fd.name, self.fs1.name, self.fs2.name, self.fs3.name)
        elif self.format == riscv_instr_format_t.CL_FORMAT:
            asm_str = "{}{}, {}({})".format(asm_str, self.fd.name, self.get_imm(), self.rs1.name)
        elif self.format == riscv_instr_format_t.CS_FORMAT:
            asm_str = "{}{}, {}({})".format(asm_str, self.fs2.name,
                                            self.get_imm(), self.rs1.name)
        else:
            logging.error("Unsupported floating point format: %0s", self.format.name)
        if self.comment != "":
            asm_str = asm_str + " #" + self.comment
        return asm_str.lower()

    def set_rand_mode(self):
        self.has_rs1 = 0
        self.has_rs2 = 0
        self.rd = 0
        self.has_imm = 0
        if self.format == riscv_instr_format_t.I_FORMAT:
            self.has_fs2 = 0
            if self.category == riscv_instr_category_t.LOAD:
                self.has_imm = 1
            elif self.instr_name.name in ['FMV_X_W', 'FMV_X_D', 'FCVT_W_S', 'FCVT_WU_S',
                                          'FCVT_L_S', 'FCVT_LU_S', 'FCVT_L_D', 'FCVT_LU_D',
                                          'FCVT_LU_S', 'FCVT_W_D', 'FCVT_WU_D']:
                self.has_fd = 0
                self.has_rd = 1
            elif self.instr_name.name in ['FMV_W_X', 'FMV_D_X', 'FCVT_S_W', 'FCVT_S_WU',
                                          'FCVT_S_L', 'FCVT_D_L', 'FCVT_S_LU', 'FCVT_D_W',
                                          'FCVT_D_LU', 'FCVT_D_WU']:
                self.has_rs1 = 1
                self.has_fs1 = 0
        elif self.format == riscv_instr_format_t.S_FORMAT:
            self.has_imm = 1
            self.has_rs1 = 1
            self.has_fs1 = 0
            self.has_fs3 = 0
        elif self.format == riscv_instr_format_t.R_FORMAT:
            if self.category == riscv_instr_category_t.COMPARE:
                self.has_rd = 1
                self.has_fd = 0
            elif self.instr_name.name in ['FCLASS_S', 'FCLASS_D']:
                self.has_rd = 1
                self.has_fd = 0
                self.has_fs2 = 0
        elif self.format == riscv_instr_format_t.R4_FORMAT:
            self.has_fs3 = 1
        elif self.format == riscv_instr_format_t.CL_FORMAT:
            self.has_imm = 1
            self.has_rs1 = 1
            self.has_fs1 = 0
            self.has_fs2 = 0
        elif self.format == riscv_instr_format_t.CS_FORMAT:
            self.has_imm = 1
            self.has_rs1 = 1
            self.has_fs1 = 0
            self.has_fd = 0
        else:
            logging.info("Unsupported format {}".format(self.format.name))

    def pre_randomize(self):
        super().pre_randomize()
        with vsc.raw_mode():
            self.fs1.rand_mode = bool(self.has_fs1)
            self.fs2.rand_mode = bool(self.has_fs2)
            self.fs3.rand_mode = bool(self.has_fs3)
            self.fd.rand_mode = bool(self.has_fd)

    # coverage related functons
    def update_src_regs(self, instruction, operands):
        if self.riscv_cov_ins is None:
            self.riscv_cov_ins = riscv_cov_instr()
        if instruction.category in ["LOAD", "CSR"]:
            self.riscv_cov_ins.update_src_regs(operands)
        if instruction.format.name == "I_FORMAT":
            logging.info("instr = {}".format(instruction.__dict__))
            if instruction.has_fs1:
                instruction.fs1 = self.get_fpr(operands[1])
                instruction.fs1_value.set_val(self.riscv_cov_ins.get_gpr_state(operands[1]))
            elif instruction.has_rs1:
                instruction.rs1 = self.riscv_cov_ins.get_gpr(operands[1])
                instruction.rs1_value = self.riscv_cov_ins.get_gpr_state(operands[1])
        elif instruction.format.name == "S_FORMAT":
            assert len(operands) == 3
            instruction.fs2 = self.get_fpr(operands[0])
            instruction.fs2_value.set_val(self.riscv_cov_ins.get_gpr_state(operands[0]))
            instruction.rs1 = self.riscv_cov_ins.get_gpr(operands[1])
            instruction.rs1_value = self.riscv_cov_ins.get_gpr_state(operands[1])
            instruction.imm = get_val(operands[2])
        elif instruction.format.name == "R_FORMAT":
            if len(operands) == 2 and instruction.instr.name in ["FSGNJ_S", "FSGNJX_S",
                                                                 "FSGNJN_S", "FSGNJ_D",
                                                                 "FSGNJX_D", "FSGNJN_D"]:
                operands.append(operands[-1])
                if instruction.has_fs2 or instruction.category.name == "CSR":
                    assert len(operands) == 3
                else:
                    assert len(operands) == 2
                if instruction.category.name != "CSR":
                    instruction.fs1 = self.get_fpr(operands[1])
                    instruction.fs1_value.set_val(self.riscv_cov_ins.get_gpr_state(operands[1]))
                    if instruction.has_fs2:
                        instruction.fs2 = self.get_fpr(operands[0])
                        instruction.fs2_value.set_val(self.riscv_cov_ins.get_gpr_state(operands[0]))
        elif instruction.format.name == "R4_FORMAT":
            assert len(operands) == 4
            instruction.fs1 = self.get_fpr(operands[1])
            instruction.fs1_value.set_val(self.riscv_cov_ins.get_gpr_state(operands[1]))
            instruction.fs2 = self.get_fpr(operands[2])
            instruction.fs2_value.set_val(self.riscv_cov_ins.get_gpr_state(operands[2]))
            instruction.fs3 = self.get_fpr(operands[3])
            instruction.fs3_value.set_val(self.riscv_cov_ins.get_gpr_state(operands[3]))
        else:
            logging.error("Unsupported format {}".format(instruction.format.name))

    def update_dst_regs(self, instruction, reg_name, val_str):
        self.riscv_cov_ins.gpr_state[reg_name] = get_val(val_str, hexa=1)
        if instruction.has_fd:
            instruction.fd = self.get_fpr(reg_name)
            instruction.fd_value.set_val(self.riscv_cov_ins.get_gpr_state(reg_name))
        elif instruction.has_rd:
            instruction.rd = self.riscv_cov_ins.get_gpr(reg_name)
            instruction.rd_value = self.riscv_cov_ins.get_gpr_state(reg_name)

    def get_fpr(self, reg_name):
        result = riscv_fpr_t[reg_name.upper()]
        return result

    def pre_sample(self, instr):
        if instr.group.name in ["RV32F", "RV64F"]:
            instr.fs1_sign = self.get_fp_operand_sign(instr.fs1_value, 31)
            instr.fs2_sign = self.get_fp_operand_sign(instr.fs2_value, 31)
            instr.fs3_sign = self.get_fp_operand_sign(instr.fs3_value, 31)
            instr.fd_sign = self.get_fp_operand_sign(instr.fd_value, 31)
        elif instr.instr.name == "FCVT_S_D":
            instr.fs1_sign = self.get_fp_operand_sign(instr.fs1_value, 63)
            instr.fd_sign = self.get_fp_operand_sign(instr.fd_value, 31)
        elif instr.instr.name == "FCVT_D_S":
            instr.fs1_sign = self.get_fp_operand_sign(instr.fs1_value, 31)
            instr.fd_sign = self.get_fp_operand_sign(instr.fd_value, 63)
        else:
            instr.fs1_sign = self.get_fp_operand_sign(instr.fs1_value, 63)
            instr.fs2_sign = self.get_fp_operand_sign(instr.fs2_value, 63)
            instr.fs3_sign = self.get_fp_operand_sign(instr.fs3_value, 63)
            instr.fd_sign = self.get_fp_operand_sign(instr.fd_value, 63)

    def get_fp_operand_sign(self, value, idx):
        if value[idx]:
            return operand_sign_e.NEGATIVE
        else:
            return operand_sign_e.POSITIVE
