# Lint as: python3
"""Tests for riscv_instr_cov."""
import sys
import os
import logging
import argparse
import vsc  # PyVSC library
import csv  # Python library to read/write from/to CSV files
from bitstring import BitArray
from pygen.pygen_src.isa.riscv_instr_cov import *
from pygen.pygen_src.riscv_instr_pkg import *
from pygen.pygen_src.target.rv32i import riscv_core_setting as rcs



logging.basicConfig(filename='logging.log',level=logging.DEBUG)

class riscv_instr():
    """ Class for a riscv instruction; data parsed from the CSV file will fill
    different fields of an instruction """
    # class attr. to keep track of reg_name:reg_value throughout the program
    gpr_state = {}
    def __init__(self, instr_name):
        self.pc = 0 # Program counter (PC) of the instruction
        self.instr = instr_name
        self.gpr = None # destination operand of the instruction
        self.csr = None
        self.binary = 0 # Instruction binary
        self.mode = None # Instruction mode
        self.trace = "None" # String representation of the instruction
        self.operands = "None"  # Instruction operands (srcss/dests)
        self.pad = None # Not used

        self.rs1_value = None
        self.rs2_value = None
        self.rs3_value = None
        self.rd_value = None
        self.fs1_value = None
        self.fs2_value = None
        self.fs3_value = None
        self.fd_value = None

        self.mem_addr = None
        self.unaligned_pc = 0
        self.unaligned_mem_access = 0
        self.compressed = 0
        self.branch_hit = 0
        self.div_result = None
        self.rs1_sign = None
        self.rs2_sign = None
        self.rs3_sign = None
        self.fs1_sign = None
        self.fs2_sign = None
        self.fs3_sign = None
        self.imm_sign = None
        self.rd_sign = None
        self.gpr_hazard = None
        self.lsu_hazard = None
        self.rs1_special_value = None
        self.rs2_special_value = None
        self.rs3_special_value = None
        self.rd_special_value = None
        self.imm_special_value = None
        self.compare_result = None
        self.logical_similarity = None

        # TODO: add & map...
        #self.imm
        #self.format
        #self.category

    def pre_sample(self):
        unaligned_pc = self.pc[-2:] != "00"
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
        if (self.format != riscv_instr_format_t.R_FORMAT and
            self.format != riscv_instr_format_t.CR_FORMAT):
            self.imm_special_value = self.get_imm_special_val(self.imm)
        if self.category in [riscv_instr_category_t.COMPARE,
                            riscv_instr_category_t.BRANCH]:
            self.compare_result = self.get_compare_result()
        if self.category in [riscv_instr_category_t.LOAD,
                             riscv_instr_category_t.STORE]:
            self.mem_addr = self.rs1_value + self.imm
            self.unaligned_mem_access = self.is_unaligned_mem_access()
            if self.unaligned_mem_access:
                logging.info("Unaligned: {}, mem_addr: {}".format(
                self.instr, self.mem_addr))
        if self.category == riscv_instr_category_t.LOGICAL:
            self.logical_similarity = self.get_logical_similarity()
        if self.category == riscv_instr_category_t.BRANCH:
            self.branch_hit = self.is_branch_hit()
        #TODO: string > enumeration
        if self.instr in ["DIV", "DIVU", "REM", "REMU", "DIVW", "DIVUW", 
                          "REMW", "REMUW"]:
            self.div_result = self.get_div_result()

    def get_operand_sign(self, operand):
        #TODO: change operand to vsc.bit_t
        out = BitArray(int=operand.val, length=rcs.XLEN)
        if out[0]:
            return operand_sign_e["NEGATIVE"]
        else:
            return operand_sign_e["POSITIVE"]

    def is_unaligned_mem_access(self):
        #TODO: string > enumeration
        if (self.instr in ["LWU", "LD", "SD", "C_LD", "C_SD"] and
            self.mem_addr % 8 != 0):
            return True
        elif (self.instr in ["LW", "SW", "C_LW", "C_SW"] and
              self.mem_addr % 4 != 0):
            return True
        elif (self.instr in ["LH", "LHU", "SH"] and
              self.mem_addr % 2 != 0):
            return True
        return False

    def get_imm_sign(self, imm):
        #TODO: change imm to vsc.int_t(32)
        out = BitArray(int=imm.val, length=rcs.XLEN)
        if out[0]:
            return operand_sign_e["NEGATIVE"]
        else:
            return operand_sign_e["POSITIVE"]

    def get_div_result(self):
        #TODO: change rs2_value to vsc.int_t(32)
        if self.rs2_value.val == 0:
            return div_result_e["DIV_BY_ZERO"]
        elif self.rs2_value.val == 1 and self.rs1_value.val == (1 << (rcs.XLEN-1)):
            return div_result_e["DIV_OVERFLOW"]
        else:
            return div_result_e["DIV_NORMAL"]

    def get_operand_special_value(self, operand):
        if operand.val == 0:
            return special_val_e["ZERO_VAL"]
        elif operand.val == 1 << (rcs.XLEN-1):
            return special_val_e["MIN_VAL"]
        elif operand.val == 1 >> 1:
            return special_val_e["MAX_VAL"]
        else:
            return special_val_e["NORMAL_VAL"]

    def get_imm_special_val(self, imm):
        if imm.val == 0:
            return special_val_e["ZERO_VAL"]
        elif self.format == riscv_instr_format_t.U_FORMAT:
            # unsigned immediate value
            # TODO: self.imm_len
            max = vsc.int_t(32, (1 << self.imm_len)-1)
            if imm.val == 0:
                return special_val_e["MIN_VAL"]
            if imm.val == max.val:
                return special_val_e["MAX_VAL"]
        else:
            # signed immediate value
            max = vsc.int_t(32, (2 ** (self.imm_len - 1)) - 1)
            min = vsc.int_t(32, -2 ** (self.imm_len - 1))
            if min.val == imm.val:
                return special_val_e["MIN_VAL"]
            if max.val == imm.val:
                return special_val_e["MAX_VAL"]
        return special_val_e["NORMAL_VAL"]

    def get_compare_result(self):
        val1 = vsc.int_t(rcs.XLEN)
        val2 = vsc.int_t(rcs.XLEN)
        val1.val = self.rs1_value.val
        val2.val = self.imm.val if (
                self.format == riscv_instr_format_t.I_FORMAT) \
            else self.rs2_value.val
        if val1.val == val2.val:
            return compare_result_e["EQUAL"]
        elif val1.val < val2.val:
            return compare_result_e["SMALLER"]
        else:
            return compare_result_e["LARGER"]

    def is_branch_hit(self):
        # TODO: string/enumeration
        if self.instr == "BEQ":
            return self.rs1_value.val == self.rs2_value.val
        elif self.instr == "C_BEQZ":
            return self.rs1_value.val == 0
        elif self.instr == "BNE":
            return self.rs1_value.val != self.rs2_value.val
        elif self.instr == "C_BNEZ":
            return self.rs1_value.val != 0
        elif self.instr == "BLT" or self.instr == "BLTU":
            return self.rs1_value.val < self.rs2_value.val
        elif self.instr == "BGE" or self.instr == "BGEU":
            return self.rs1_value.val >= self.rs2_value.val
        else:
            logging.error("Unexpected instruction {}".format(self.instr))

    def get_logical_similarity(self):
        val1 = vsc.int_t(rcs.XLEN, self.rs1_value.val)
        val2 = vsc.int_t(rcs.XLEN)
        val2.val = (self.imm.val if self.format == riscv_instr_format_t.I_FORMAT
                    else self.rs2_value.val)
        temp = bin(val1.val ^ val2.val)
        bit_difference = len([[ones for ones in temp[2:] if ones=='1']])
        if val1.val == val2.val:
            return logical_similarity_e["IDENTICAL"]
        elif bit_difference == 32:
            return logical_similarity_e["OPPOSITE"]
        elif bit_difference < 5:
            return logical_similarity_e["SIMILAR"]
        else:
            return logical_similarity_e["DIFFERENT"]

    def check_hazard_condition(self, pre_instr):
        # TODO: has_rd(), has_rs1, has_rs2, rd, category, convert2asm (from IG)
        if pre_instr.has_rd():
            if ((self.has_rs1 and self.rs1 == pre_instr.rd) or
                    (self.has_rs2 and self.rs1 == pre_instr.rd)):
                self.gpr_hazard = hazard_e["RAW_HAZARD"]
            elif self.has_rd and self.rd == pre_instr.rd:
                self.gpr_hazard = hazard_e["WAW_HAZARD"]
            elif (self.has_rd and
                  ((pre_instr.has_rs1 and (pre_instr.rs1 == self.rd)) or
                   (pre_instr.has_rs2 and (pre_instr.rs2 == self.rd)))):
                self.gpr_hazard = hazard_e["WAR_HAZARD"]
            else:
                self.gpr_hazard = hazard_e["NO_HAZARD"]
        if self.category == riscv_instr_category_t.LOAD:
            # TODO: change mem_addr to vsc type
            if (pre_instr.category == riscv_instr_category_t.STORE and
                    pre_instr.mem_addr == self.mem_addr):
                self.lsu_hazard = hazard_e["RAW_HAZARD"]
            else:
                self.lsu_hazard = hazard_e["NO_HAZARD"]
        if self.category == riscv_instr_category_t.STORE:
            if (pre_instr.category == riscv_instr_category_t.STORE and
                    pre_instr.mem_addr == self.mem_addr):
                self.lsu_hazard = hazard_e["WAW_HAZARD"]
            elif (pre_instr.category == riscv_instr_category_t.LOAD and
                    pre_instr.mem_addr == self.mem_addr):
                self.lsu_hazard = hazard_e["WAR_HAZARD"]
            else:
                self.lsu_hazard = hazard_e["NO_HAZARD"]
        logging.info("Pre: {}, Cur: {}, Hazard: {}/{}".format(
            pre_instr.convert2asm(), self.convert2asm(),
            self.gpr_hazard.name, self.lsu_hazard.name))

    def update_src_regs(self, operands):
        pass

    def update_dst_regs(self, reg_name, val_str):
        pass

class riscv_instr_cov_test():
    """ Main class for applying the functional coverage test """
    def __init__(self, argv):
        self.trace = {}
        self.csv_trace = argv
        self.entry_cnt, self.total_entry_cnt, self.skipped_cnt, \
        self.unexpected_illegal_instr_cnt = 0, 0, 0, 0

    def run_phase(self):
        if not self.csv_trace:
            sys.exit("No CSV file found!")
        logging.info("{} CSV trace files to be "
                     "processed...\n".format(len(self.csv_trace)))
        expect_illegal_instr = False
        # Assuming we get list of csv files pathname from cov.py in argv
        for csv_file in self.csv_trace:
            with open("{}".format(csv_file)) as trace_file:
                self.entry_cnt = 0
                header = []
                entry = []
                csv_reader = csv.reader(trace_file, delimiter=',')
                line_count = 0
                # Get the header line
                for row in csv_reader:
                    if line_count == 0:
                        header = row
                        logging.info("Header: {}".format(header))
                    else:
                        entry = row
                        if len(entry) != len(header):
                            logging.info("Skipping malformed entry[{}]: "
                                         "[{}]".format(self.entry_cnt, entry))
                            self.skipped_cnt += 1
                        else:
                            self.trace["csv_entry"] = row
                            for idx in range(len(header)):
                                if "illegal" in entry[idx]:
                                    expect_illegal_instr = True
                                self.trace[header[idx]] = entry[idx]
                                if header[idx] != "pad":
                                    logging.info("{} = {}".format(header[idx],
                                                                  entry[idx])) 
                            self.post_process_trace()
                            if self.trace["instr"] in ["li", "ret", "la"]:
                                pass
                            if "amo" in self.trace["instr"] or \
                               "lr" in self.trace["instr"] or \
                               "sc" in self.trace["instr"]:
                                # TODO: Enable functional coverage for AMO test
                                pass
                            if not self.sample():
                                if not expect_illegal_instr:
                                    logging.error("Found unexpected illegal "
                                                  "instr: {} "
                                                  "[{}]".format(self.trace[
                                                      "instr"],entry))
                                    self.unexpected_illegal_instr_cnt += 1
                        self.entry_cnt += 1
                    line_count += 1
                logging.info("[{}]: {} instr processed".format(csv_file,
                                                               self.entry_cnt))
                self.total_entry_cnt += self.entry_cnt
        logging.info("Finished processing {} trace CSV, {} "
                     "instructions".format(len(self.csv_trace),
                                          self.total_entry_cnt))
        if self.skipped_cnt > 0 or self.unexpected_illegal_instr_cnt > 0:
            logging.error("{} instruction skipped, {} illegal "
                          "instructions".format(self.skipped_cnt),
                          self.unexpected_illegal_instr_cnt)

    def post_process_trace(self):
        pass

    def sample(self):
        instr_name, binary = "", ""
        binary = get_val(self.trace["binary"], hexa=1)
        if binary[-2:] != "11": #TODO: and RV32C in supported_isa 
            #TODO: sample compressed instruction
            pass
        if binary[-2:] == "11":
            #TODO: sampling
            pass
        #TODO: buch of if statements to check if the instruction name is valid
        # and is a member of registered ones
        instr_name = self.process_instr_name(self.trace["instr"])
        instruction = riscv_instr(instr_name)
        #TODO: check the instruction group...
        self.assign_trace_info_to_instr(instruction)
        #TODO: instruction.pre_sample() and sample(instruction)
        return True

    def assign_trace_info_to_instr(self, instruction):
        operands, gpr_update, pair = [], [], []
        instruction.pc = get_val(self.trace["pc"], hexa=1)
        instruction.binary = get_val(self.trace["binary"], hexa=1)
        instruction.gpr = self.trace["gpr"]
        instruction.csr = self.trace["csr"]
        instruction.mode = self.trace["mode"]
        instruction.trace = self.trace["instr_str"]
        instruction.operands = self.trace["operand"]
        operands = self.trace["operand"].split(",")
        instruction.update_src_regs(operands)
        gpr_update = self.trace["gpr"].split(";")
        if len(gpr_update) == 1 and gpr_update[0] == "": 
            gpr_update = []
        for dest in gpr_update:
            pair = dest.split(":")
            if len(pair) != 2:
                logging.error("Illegal gpr update format: {}".format(dest))
            instruction.update_dst_regs(pair[0], pair[1])
        instruction.pad = self.trace["pad"]

    def process_instr_name(self, instruction):
        instruction = instruction.upper()
        instruction.replace(".", "_")
        instruction = self.update_instr_name(instruction)
        return instruction

    def update_instr_name(self, instruction):
        switcher = {
            # Rename to new name as ovpsim still uses old name
            "FMV_S_X": "FMV_W_X",
            "FMV_X_S": "FMV_X_W",
            # Convert pseudoinstructions
            "FMV_S":  "FSGNJ_S",
            "FABS_S": "FSGNJX_S",
            "FNEG_S": "FSGNJN_S",
            "FMV_D":  "FSGNJ_D",
            "FABS_D": "FSGNJX_D",
            "FNEG_D": "FSGNJN_D",
        }
        # if instruction is not present in the dictionary,second argument well
        # be assigned as default value of passed argument
        instruction = switcher.get(instruction, instruction)
        return instruction


def main(argv): 
    cov_test = riscv_instr_cov_test(argv)
    cov_test.run_phase()

if __name__ == "__main__":
    main(sys.argv)
