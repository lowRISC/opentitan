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
from pygen_src.riscv_instr_pkg import (pkg_ins, riscv_fpr_t, riscv_instr_format_t,
                                       riscv_instr_category_t)


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
            logging.info("Unsupported format %0s", self.format.name)

    def pre_randomize(self):
        super().pre_randomize()
        with vsc.raw_mode():
            self.fs1.rand_mode = bool(self.has_fs1)
            self.fs2.rand_mode = bool(self.has_fs2)
            self.fs3.rand_mode = bool(self.has_fs3)
            self.fd.rand_mode = bool(self.has_fd)

    # coverage related functons
    def update_src_regs(self, operands = []):
        pass

    def update_dst_regs(self, reg_name, val_str):
        pass

    def get_fpr(self, reg_name):
        pass

    def get_pre_sample(self):
        pass

    def get_fp_operand_sign(self, value, idx):
        pass

    def check_hazard_condition(self, pre_instr):
        pass
