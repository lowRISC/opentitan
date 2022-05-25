"""Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
"""

import vsc
import logging
from importlib import import_module
from enum import IntEnum, auto
from pygen_src.riscv_instr_pkg import *
from pygen_src.riscv_instr_gen_config import cfg
rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")


class operand_sign_e(IntEnum):
    POSITIVE = 0
    NEGATIVE = auto()


class div_result_e(IntEnum):
    DIV_NORMAL = 0
    DIV_BY_ZERO = auto()
    DIV_OVERFLOW = auto()


class div_result_ex_overflow_e(IntEnum):
    DIV_NORMAL = 0
    DIV_BY_ZERO = auto()


class compare_result_e(IntEnum):
    EQUAL = 0
    LARGER = auto()
    SMALLER = auto()


class logical_similarity_e(IntEnum):
    IDENTICAL = 0
    OPPOSITE = auto()
    SIMILAR = auto()
    DIFFERENT = auto()


class special_val_e(IntEnum):
    NORMAL_VAL = 0
    MIN_VAL = auto()
    MAX_VAL = auto()
    ZERO_VAL = auto()


class riscv_cov_instr:
    """ Class for a riscv instruction in functional coverage phase;
    data parsed from the CSV file fill different fields of an instruction """
    # class attr. to keep track of reg_name:reg_value throughout the program
    gpr_state = {}

    def __init__(self):
        # Program counter (PC) of the instruction
        self.pc = vsc.bit_t(rcs.XLEN)
        self.instr = None
        # self.gpr = None  # destination operand of the instruction
        self.binary = vsc.bit_t(32)  # Instruction binary
        # self.mode = None  # Instruction mode
        self.trace = "None"  # String representation of the instruction
        # self.operands = "None"  # Instruction operands (srcss/dests)
        # self.pad = None  # Not used

        self.rs1_value = vsc.bit_t(rcs.XLEN)
        self.rs2_value = vsc.bit_t(rcs.XLEN)
        self.rs3_value = vsc.bit_t(rcs.XLEN)
        self.rd_value = vsc.bit_t(rcs.XLEN)
        self.fs1_value = vsc.bit_t(rcs.XLEN)
        self.fs2_value = vsc.bit_t(rcs.XLEN)
        self.fs3_value = vsc.bit_t(rcs.XLEN)
        self.fd_value = vsc.bit_t(rcs.XLEN)

        self.mem_addr = vsc.int_t(rcs.XLEN)
        self.unaligned_pc = 0
        self.unaligned_mem_access = 0
        self.compressed = 0
        self.branch_hit = 0
        self.div_result = None
        self.rs1_sign = 0
        self.rs2_sign = 0
        self.rs3_sign = 0
        self.fs1_sign = 0
        self.fs2_sign = 0
        self.fs3_sign = 0
        self.imm_sign = 0
        self.rd_sign = 0
        self.fd_sign = 0
        self.gpr_hazard = hazard_e.NO_HAZARD
        self.lsu_hazard = hazard_e.NO_HAZARD
        self.rs1_special_value = 0
        self.rs2_special_value = 0
        self.rs3_special_value = 0
        self.rd_special_value = 0
        self.imm_special_value = 0
        self.compare_result = 0
        self.logical_similarity = 0

        self.group = None
        self.format = None
        self.category = None
        self.imm_type = None

        self.csr = vsc.bit_t(12)
        ''' TODO: rs2, rs1, rd, group, format, category, imm_type
            fs1, fs2, fs3, fd will be changed to vsc.enum_t once
            the issue with set/get_val is fixed '''
        self.rs2 = 0
        self.rs1 = 0
        self.rd = 0
        self.imm = vsc.int_t(32)
        self.has_rs1 = 1
        self.has_rs2 = 1
        self.has_rd = 1
        self.has_imm = 1
        self.imm_len = 0
        self.has_fs1 = 1
        self.has_fs2 = 1
        self.has_fs3 = 0
        self.has_fd = 1
        self.fs1 = 0
        self.fs2 = 0
        self.fs3 = 0
        self.fd = 0

    def assign_attributes(self):
        attr_list = get_attr_list(self.instr)
        self.format = attr_list[0]
        self.category = attr_list[1]
        self.group = attr_list[2]
        self.imm_type = imm_t.IMM
        if len(attr_list) > 3:
            self.imm_type = attr_list[3]
        self.set_imm_len()
        self.set_mode()
        if self.group.name in ["RV32D", "RV32F"]:
            self.set_fd_mode()

    def set_imm_len(self):
        if self.format.name in ["U_FORMAT", "J_FORMAT"]:
            self.imm_len = 20
        elif self.format.name in ["I_FORMAT", "S_FORMAT", "B_FORMAT"]:
            if self.imm_type.name == "UIMM":
                self.imm_len = 5
            else:
                self.imm_len = 12

    def set_mode(self):
        # mode setting for Instruction Format
        if self.format.name == "R_FORMAT":
            self.has_imm = 0
        if self.format.name == "I_FORMAT":
            self.has_rs2 = 0
        if self.format.name in ["S_FORMAT", "B_FORMAT"]:
            self.has_rd = 0
        if self.format.name in ["U_FORMAT", "J_FORMAT"]:
            self.has_rs1 = 0
            self.has_rs2 = 0

        # mode setting for Instruction Category
        if self.category.name == "CSR":
            self.has_rs2 = 0
            if self.format.name == "I_FORMAT":
                self.has_rs1 = 0

    # mode setting for F and D Instruction
    def set_fd_mode(self):
        if self.format == riscv_instr_format_t.I_FORMAT:
            self.has_fs2 = 0
            if self.category == riscv_instr_category_t.LOAD:
                self.has_imm = 1
            elif self.instr.name in ['FMV_X_W', 'FMV_X_D', 'FCVT_W_S', 'FCVT_WU_S',
                                     'FCVT_L_S', 'FCVT_LU_S', 'FCVT_L_D', 'FCVT_LU_D',
                                     'FCVT_LU_S', 'FCVT_W_D', 'FCVT_WU_D']:
                self.has_fd = 0
                self.has_rd = 1
            elif self.instr.name in ['FMV_W_X', 'FMV_D_X', 'FCVT_S_W', 'FCVT_S_WU',
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
            elif self.instr.name in ['FCLASS_S', 'FCLASS_D']:
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

    def pre_sample(self):
        unaligned_pc = self.pc.get_val() % 4 != 0
        self.rs1_sign = self.get_operand_sign(self.rs1_value)
        self.rs2_sign = self.get_operand_sign(self.rs2_value)
        self.rs3_sign = self.get_operand_sign(self.rs3_value)
        self.rd_sign = self.get_operand_sign(self.rd_value)
        self.fs1_sign = self.get_operand_sign(self.fs1_value)
        self.fs2_sign = self.get_operand_sign(self.fs2_value)
        self.fs3_sign = self.get_operand_sign(self.fs3_value)
        self.fd_sign = self.get_operand_sign(self.fd_value)
        self.imm_sign = self.get_imm_sign(self.imm)
        self.rs1_special_value = self.get_operand_special_value(self.rs1_value)
        self.rd_special_value = self.get_operand_special_value(self.rd_value)
        self.rs2_special_value = self.get_operand_special_value(self.rs2_value)
        self.rs3_special_value = self.get_operand_special_value(self.rs3_value)
        if self.format.name not in ["R_FORMAT", "CR_FORMAT"]:
            self.imm_special_value = self.get_imm_special_val(self.imm)
        if self.category.name in ["COMPARE", "BRANCH"]:
            self.compare_result = self.get_compare_result()
        if self.category.name in ["LOAD", "STORE"]:
            self.mem_addr.set_val(self.rs1_value.get_val() +
                                  self.imm.get_val())
            self.unaligned_mem_access = self.is_unaligned_mem_access()
            if self.unaligned_mem_access:
                logging.info("Unaligned: {}, mem_addr: {}".format(
                    self.instr.name, self.mem_addr.get_val()))
        if self.category.name == "LOGICAL":
            self.logical_similarity = self.get_logical_similarity()
        if self.category.name == "BRANCH":
            self.branch_hit = self.is_branch_hit()
        if self.instr.name in ["DIV", "DIVU", "REM", "REMU", "DIVW", "DIVUW",
                               "REMW", "REMUW"]:
            self.div_result = self.get_div_result()

    @staticmethod
    def get_operand_sign(operand):
        # TODO: Currently handled using string formatting as part select
        #  isn't yet supported for global vsc variables
        operand_bin = format(operand.get_val(), '#0{}b'.format(rcs.XLEN + 2))
        # "0b" is the prefix, so operand_bin[2] is the sign bit
        if operand_bin[2] == "0":
            return operand_sign_e["POSITIVE"]
        else:
            return operand_sign_e["NEGATIVE"]

    def is_unaligned_mem_access(self):
        if (self.instr.name in ["LWU", "LD", "SD", "C_LD", "C_SD"] and
                self.mem_addr.get_val() % 8 != 0):
            return 1
        elif (self.instr.name in ["LW", "SW", "C_LW", "C_SW"] and
              self.mem_addr.get_val() % 4 != 0):
            return 1
        elif (self.instr.name in ["LH", "LHU", "SH"] and
              self.mem_addr.get_val() % 2 != 0):
            return 1
        return 0

    @staticmethod
    def get_imm_sign(imm):
        # TODO: Currently handled using string formatting as part select
        #  isn't yet supported for global vsc variables
        imm_bin = format(imm.get_val(), '#0{}b'.format(rcs.XLEN + 2))
        # "0b" is the prefix, so imm_bin[2] is the sign bit
        if imm_bin[2] == "0":
            return operand_sign_e["POSITIVE"]
        else:
            return operand_sign_e["NEGATIVE"]

    def get_div_result(self):
        if self.rs2_value.get_val() == 0:
            return div_result_e["DIV_BY_ZERO"]
        elif (self.rs2_value.get_val() == 1
              and self.rs1_value.get_val() == (1 << (rcs.XLEN - 1))):
            return div_result_e["DIV_OVERFLOW"]
        else:
            return div_result_e["DIV_NORMAL"]

    @staticmethod
    def get_operand_special_value(operand):
        if operand.get_val() == 0:
            return special_val_e["ZERO_VAL"]
        elif operand.get_val() == 1 << (rcs.XLEN - 1):
            return special_val_e["MIN_VAL"]
        elif operand.get_val() == 1 >> 1:
            return special_val_e["MAX_VAL"]
        else:
            return special_val_e["NORMAL_VAL"]

    def get_imm_special_val(self, imm):
        if imm.get_val() == 0:
            return special_val_e["ZERO_VAL"]
        elif self.format == riscv_instr_format_t.U_FORMAT:
            # unsigned immediate value
            max_val = vsc.int_t(32, (1 << self.imm_len) - 1)
            if imm.get_val() == 0:
                return special_val_e["MIN_VAL"]
            if imm.get_val() == max_val.get_val():
                return special_val_e["MAX_VAL"]
        else:
            # signed immediate value
            max_val = vsc.int_t(32, (2 ** (self.imm_len - 1)) - 1)
            min_val = vsc.int_t(32, -2 ** (self.imm_len - 1))
            if min_val.get_val() == imm.get_val():
                return special_val_e["MIN_VAL"]
            if max_val.get_val() == imm.get_val():
                return special_val_e["MAX_VAL"]
        return special_val_e["NORMAL_VAL"]

    def get_compare_result(self):
        val1 = vsc.int_t(rcs.XLEN, self.rs1_value.get_val())
        val2 = vsc.int_t(rcs.XLEN, self.imm.get_val() if (
                self.format == riscv_instr_format_t.I_FORMAT) else
        self.rs2_value.val)
        if val1.get_val() == val2.get_val():
            return compare_result_e["EQUAL"]
        elif val1.get_val() < val2.get_val():
            return compare_result_e["SMALLER"]
        else:
            return compare_result_e["LARGER"]

    def is_branch_hit(self):
        if self.instr.name == "BEQ":
            return int(self.rs1_value.get_val() == self.rs2_value.get_val())
        elif self.instr.name == "C_BEQZ":
            return int(self.rs1_value.get_val() == 0)
        elif self.instr.name == "BNE":
            return int(self.rs1_value.get_val() != self.rs2_value.get_val())
        elif self.instr.name == "C_BNEZ":
            return int(self.rs1_value.get_val() != 0)
        elif self.instr.name == "BLT" or self.instr.name == "BLTU":
            return int(self.rs1_value.get_val() < self.rs2_value.get_val())
        elif self.instr.name == "BGE" or self.instr.name == "BGEU":
            return int(self.rs1_value.get_val() >= self.rs2_value.get_val())
        else:
            logging.error("Unexpected instruction {}".format(self.instr.name))

    def get_logical_similarity(self):
        val1 = vsc.int_t(rcs.XLEN, self.rs1_value.get_val())
        val2 = vsc.int_t(rcs.XLEN, (self.imm.get_val() if
                                    self.format == riscv_instr_format_t.I_FORMAT
                                    else self.rs2_value.val))
        temp = bin(val1.get_val() ^ val2.get_val())
        bit_difference = len([[ones for ones in temp[2:] if ones == '1']])
        if val1.get_val() == val2.get_val():
            return logical_similarity_e["IDENTICAL"]
        elif bit_difference == 32:
            return logical_similarity_e["OPPOSITE"]
        elif bit_difference < 5:
            return logical_similarity_e["SIMILAR"]
        else:
            return logical_similarity_e["DIFFERENT"]

    def check_hazard_condition(self, pre_instr):
        '''TODO: There are cases where instruction actually has destination but
        ovpsim doesn't log it because of no change in its value. Hence,
        the result of the check_hazard_condition won't be accurate. Need to
        explicitly extract the destination register from the operands '''
        if pre_instr.has_rd:
            if ((self.has_rs1 and (self.rs1 == pre_instr.rd)) or
                    (self.has_rs2 and (self.rs2 == pre_instr.rd))):
                logging.info("pre_instr {}".format(pre_instr.instr.name))
                self.gpr_hazard = hazard_e["RAW_HAZARD"]
            elif self.has_rd and (self.rd == pre_instr.rd):
                self.gpr_hazard = hazard_e["WAW_HAZARD"]
            elif (self.has_rd and
                  ((pre_instr.has_rs1 and (pre_instr.rs1 == self.rd)) or
                   (pre_instr.has_rs2 and (pre_instr.rs2 == self.rd)))):
                self.gpr_hazard = hazard_e["WAR_HAZARD"]
            else:
                self.gpr_hazard = hazard_e["NO_HAZARD"]
        if self.category == riscv_instr_category_t.LOAD:
            if (pre_instr.category == riscv_instr_category_t.STORE and
                    (pre_instr.mem_addr.get_val() == self.mem_addr.get_val())):
                self.lsu_hazard = hazard_e["RAW_HAZARD"]
            else:
                self.lsu_hazard = hazard_e["NO_HAZARD"]
        if self.category == riscv_instr_category_t.STORE:
            if (pre_instr.category == riscv_instr_category_t.STORE and
                    (pre_instr.mem_addr.get_val() == self.mem_addr.get_val())):
                self.lsu_hazard = hazard_e["WAW_HAZARD"]
            elif (pre_instr.category == riscv_instr_category_t.LOAD and
                  (pre_instr.mem_addr.get_val() == self.mem_addr.get_val())):
                self.lsu_hazard = hazard_e["WAR_HAZARD"]
            else:
                self.lsu_hazard = hazard_e["NO_HAZARD"]
        # Hazard Condition check for RV32D and RV32F instructions
        if pre_instr.has_fd:
            if ((self.has_fs1 and (self.fs1 == pre_instr.fd)) or
                 (self.has_fs2 and (self.fs2 == pre_instr.fd)) or
                 (self.has_fs3 and (self.fs3 == pre_instr.fd))):
                self.gpr_hazard = hazard_e["RAW_HAZARD"]
            elif (self.has_fd and (self.fd == pre_instr.fd)):
                self.gpr_hazard = hazard_e["WAW_HAZARD"]
            elif (self.has_fd and ((pre_instr.has_fs1 and (pre_instr.fs1 == self.fd)) or
                                      (pre_instr.has_fs2 and (pre_instr.fs2 == self.fd)) or
                                      (pre_instr.has_fs3 and (pre_instr.fs3 == self.fd)))):
                self.gpr_hazard = hazard_e["WAR_HAZARD"]
            else:
                self.gpr_hazard = hazard_e["NO_HAZARD"]
        logging.debug("Pre PC/name: {}/{}, Cur PC/name: {}/{}, "
                      "Hazard: {}/{}".format(pre_instr.pc.get_val(),
                                             pre_instr.instr.name,
                                             self.pc.get_val(),
                                             self.instr.name,
                                             self.gpr_hazard.name,
                                             self.lsu_hazard.name))

    def get_instr_name(self):
        get_instr_name = self.instr.name
        for i in get_instr_name:
            if i == "_":
                get_instr_name = get_instr_name.replace(i, ".")
        return get_instr_name

    def update_src_regs(self, operands):
        if self.format.name in ["J_FORMAT", "U_FORMAT"]:
            # instr rd,imm
            assert len(operands) == 2
            self.imm.set_val(get_val(operands[1]))
        elif self.format.name == "I_FORMAT":
            assert len(operands) == 3
            if self.category.name == "LOAD":
                # load rd, imm(rs1)
                self.rs1 = self.get_gpr(operands[2])
                self.rs1_value.set_val(self.get_gpr_state(operands[2]))
                self.imm.set_val(get_val(operands[1]))
            elif self.category.name == "CSR":
                # csrrwi rd, csr, imm
                self.imm.set_val(get_val(operands[2]))
                if operands[1].upper() in privileged_reg_t.__members__:
                    self.csr.set_val(
                        privileged_reg_t[operands[1].upper()].value)
                else:
                    self.csr.set_val(get_val(operands[1]))
            else:
                # addi rd, rs1, imm
                self.rs1 = self.get_gpr(operands[1])
                self.rs1_value.set_val(self.get_gpr_state(operands[1]))
                self.imm.set_val(get_val(operands[2]))
        elif self.format.name in ["S_FORMAT", "B_FORMAT"]:
            assert len(operands) == 3
            if self.category.name == "STORE":
                self.rs2 = self.get_gpr(operands[0])
                self.rs2_value.set_val(self.get_gpr_state(operands[0]))
                self.rs1 = self.get_gpr(operands[2])
                self.rs1_value.set_val(self.get_gpr_state(operands[2]))
                self.imm.set_val(get_val(operands[1]))
            else:
                # bne rs1, rs2, imm
                self.rs1 = self.get_gpr(operands[0])
                self.rs1_value.set_val(self.get_gpr_state(operands[0]))
                self.rs2 = self.get_gpr(operands[1])
                self.rs2_value.set_val(self.get_gpr_state(operands[1]))
                self.imm.set_val(get_val(operands[2]))
        elif self.format.name == "R_FORMAT":
            if self.has_rs2 or self.category.name == "CSR":
                assert len(operands) == 3
            else:
                assert len(operands) == 2
            if self.category.name == "CSR":
                # csrrw rd, csr, rs1
                if operands[1].upper() in privileged_reg_t.__members__:
                    self.csr.set_val(
                        privileged_reg_t[operands[1].upper()].value)
                else:
                    self.csr.set_val(get_val(operands[1]))
                self.rs1 = self.get_gpr(operands[2])
                self.rs1_value.set_val(self.get_gpr_state(operands[2]))
            else:
                # add rd, rs1, rs2
                self.rs1 = self.get_gpr(operands[1])
                self.rs1_value.set_val(self.get_gpr_state(operands[1]))
                if self.has_rs2:
                    self.rs2 = self.get_gpr(operands[2])
                    self.rs2_value.set_val(self.get_gpr_state(operands[2]))
        elif self.format.name == "R4_FORMAT":
            assert len(operands) == 4
            self.rs1 = self.get_gpr(operands[1])
            self.rs1_value.set_val(self.get_gpr_state(operands[1]))
            self.rs2 = self.get_gpr(operands[2])
            self.rs2_value.set_val(self.get_gpr_state(operands[2]))
            self.rs2 = self.get_gpr(operands[3])
            self.rs2_value.set_val(self.get_gpr_state(operands[3]))
        elif self.format.name in ["CI_FORMAT", "CIW_FORMAT"]:
            if self.instr.name == "C_ADDI16SP":
                self.imm.set_val(get_val(operands[1]))
                self.rs1 = riscv_reg_t.SP
                self.rs1_value.set_val(self.get_gpr_state("sp"))
            elif self.instr.name == "C_ADDI4SPN":
                self.rs1 = riscv_reg_t.SP
                self.rs1_value.set_val(self.get_gpr_state("sp"))
            elif self.instr.name in ["C_LDSP", "C_LWSP", "C_LQSP"]:
                # c.ldsp rd, imm
                self.imm.set_val(get_val(operands[1]))
                self.rs1 = riscv_reg_t.SP
                self.rs1_value.set_val(self.get_gpr_state("sp"))
            else:
                # c.lui rd, imm
                self.imm.set_val(get_val(operands[1]))
        elif self.format.name == "CL_FORMAT":
            # c.lw rd, imm(rs1)
            self.imm.set_val(get_val(operands[1]))
            self.rs1 = self.get_gpr(operands[2])
            self.rs1_value.set_val(self.get_gpr_state(operands[2]))
        elif self.format.name == "CS_FORMAT":
            # c.sw rs2,imm(rs1)
            self.rs2 = self.get_gpr(operands[0])
            self.rs2_value.set_val(self.get_gpr_state(operands[0]))
            self.rs1 = self.get_gpr(operands[2])
            self.rs1_value.set_val(self.get_gpr_state(operands[2]))
            self.imm.set_val(get_val(operands[1]))
        elif self.format.name == "CA_FORMAT":
            # c.and rd, rs2 (rs1 == rd)
            self.rs2 = self.get_gpr(operands[1])
            self.rs2_value.set_val(self.get_gpr_state(operands[1]))
            self.rs1 = self.get_gpr(operands[0])
            self.rs1_value.set_val(self.get_gpr_state(operands[0]))
        elif self.format.name == "CB_FORMAT":
            # c.beqz rs1, imm
            self.rs1 = self.get_gpr(operands[0])
            self.rs1_value.set_val(self.get_gpr_state(operands[0]))
            self.imm.set_val(get_val(operands[1]))
        elif self.format.name == "CSS_FORMAT":
            # c.swsp rs2, imm
            self.rs2 = self.get_gpr(operands[0])
            self.rs2_value.set_val(self.get_gpr_state(operands[0]))
            self.rs1 = riscv_reg_t.SP
            self.rs1_value.set_val(self.get_gpr_state("sp"))
            self.imm.set_val(get_val(operands[1]))
        elif self.format.name == "CR_FORMAT":
            if self.instr.name in ["C_JR", "C_JALR"]:
                # c.jalr rs1
                self.rs1 = self.get_gpr(operands[0])
                self.rs1_value.set_val(self.get_gpr_state(operands[0]))
            else:
                # c.add rd, rs2
                self.rs2 = self.get_gpr(operands[1])
                self.rs2_value.set_val(self.get_gpr_state(operands[1]))
        elif self.format.name == "CJ_FORMAT":
            # c.j imm
            self.imm.set_val(get_val(operands[0]))
        else:
            logging.error("Unsupported format {}".format(self.format.name))

    def update_dst_regs(self, reg_name, val_str):
        riscv_cov_instr.gpr_state[reg_name] = get_val(val_str, hexa=1)
        self.rd = self.get_gpr(reg_name)
        self.rd_value.set_val(self.get_gpr_state(reg_name))

    @staticmethod
    def get_gpr(reg_name):
        reg_name = reg_name.upper()
        if reg_name not in riscv_reg_t.__members__:
            logging.error("Cannot convert {} to GPR".format(reg_name))
        return riscv_reg_t[reg_name]

    @staticmethod
    def get_gpr_state(name):
        if name in ["zero", "x0"]:
            return 0
        elif name in riscv_cov_instr.gpr_state:
            return riscv_cov_instr.gpr_state[name]
        else:
            logging.warning(
                "Cannot find GPR state: {}; initialize to 0".format(name))
            if name.upper() in riscv_reg_t.__members__:
                riscv_cov_instr.gpr_state[name] = 0
            return 0
