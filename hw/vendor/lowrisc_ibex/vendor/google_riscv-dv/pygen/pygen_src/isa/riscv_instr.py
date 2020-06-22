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
See the License for the specific language governing permissions and
limitations under the License.
Regression script for RISC-V random instruction generator

"""


from collections import defaultdict
from pygen_src.riscv_instr_gen_config import riscv_instr_gen_config
from pygen_src.riscv_instr_pkg import riscv_instr_group_t
from pygen_src.isa import rv32i_instr  # NOQA
import random
from bitstring import BitArray
import logging
from copy import copy
import sys


class riscv_instr:

    logging.basicConfig(level=logging.INFO)
    instr_registry = {}

    def __init__(self):
        self.instr_names = []
        self.instr_group = defaultdict(list)
        self.instr_category = defaultdict(list)
        self.basic_instr = []
        self.instr_template = {}

        self.exclude_reg = []
        self.include_reg = []

        self.group = None
        self.format = None
        self.category = None
        self.instr_name = None
        self.imm_type = None
        self.imm_len = 0

        self.csr = None
        self.rs2 = None
        self.rs1 = None
        self.rd = None
        self.imm = BitArray(hex="0x00000000")

        self.imm_mask = BitArray(hex="0xffffffff")
        self.is_branch_target = None
        self.has_label = 1
        self.atomic = 0
        self.branch_assigned = None
        self.process_load_store = 1
        self.is_compressed = None
        self.is_illegal_instr = None
        self.is_hint_instr = None
        self.is_floating_point = None
        self.imm_str = None
        self.comment = None
        self.label = None
        self.is_local_numeric_label = None
        self.idx = -1
        self.has_rs1 = 1
        self.has_rs2 = 1
        self.has_rd = 1
        self.has_imm = 1

        # Fields Added for debugging These fields are actually from a different files.
        self.unsupported_instr = []
        self.XLEN = 32
        self.supported_isa = [riscv_instr_group_t.RV32I]
        self.implemented_csr = []

    @classmethod
    def register(cls, instr_name):
        logging.info("Registering %s", instr_name.name)
        cls.instr_registry[instr_name.name] = 1
        if(instr_name is None):
            print("\n")
        return 1

    def create_instr_list(self, cfg):
        self.instr_names.clear()
        self.instr_group.clear()
        self.instr_category.clear()
        for instr_name, values in self.instr_registry.items():
            if(instr_name in self.unsupported_instr):
                continue
            instr_inst = self.create_instr(instr_name)
            self.instr_template[instr_name] = instr_inst

            if (not instr_inst.is_supported(cfg)):
                continue
            if ((self.XLEN != 32) and (instr_name == "C_JAL")):
                continue
            if (("SP" in cfg.reserved_regs) and (instr_name == "C_ADDI16SP")):
                continue
            if (cfg.enable_sfence and instr_name == "SFENCE_VMA"):
                continue
            if (instr_name in ["FENCE", "FENCE_I", "SFENCE_VMA"]):
                continue
            if (instr_inst.group in self.supported_isa and
                    not(cfg.disable_compressed_instr and
                        instr_inst.group in ["RV32C", "RV64C", "RV32DC", "RV32FC", "RV128C"]) and
                    not(not(cfg.enable_floating_point) and instr_inst.group in
                        ["RV32F", "RV64F", "RV32D", "RV64D"])):
                self.instr_category[instr_inst.category.name].append(instr_name)
                self.instr_group[instr_inst.group.name].append(instr_name)
                self.instr_names.append(instr_name)

        self.build_basic_instruction_list(cfg)
        self.create_csr_filter(cfg)

    def create_instr(self, instr_name):
        """TODO This method is specific to RV32I instruction only.
        It must be scaled to all instruction extensions."""
        try:
            instr_inst = eval("rv32i_instr.riscv_" + instr_name + "_instr()")
        except Exception:
            logging.critical("Failed to create instr: %0s", instr_name)
            sys.exit(1)
        return instr_inst

    def is_supported(self, cfg):
        return 1

    def build_basic_instruction_list(self, cfg):
        self.basic_instr = (self.instr_category["SHIFT"] + self.instr_category["ARITHMETIC"] +
                            self.instr_category["LOGICAL"] + self.instr_category["COMPARE"])
        if(cfg.no_ebreak == 0):
            self.basic_instr.append("EBREAK")
            for items in self.supported_isa:
                if("RV32C" in self.supported_isa and not(cfg.disable_compressed_instr)):
                    self.basic_instr.append("C_EBREAK")
                    break
        if(cfg.no_dret == 0):
            self.basic_instr.append("DRET")
        if(cfg.no_fence == 0):
            self.basic_instr.append(self.instr_category["SYNCH"])
        if(cfg.no_csr_instr == 0 and cfg.init_privileged_mode == "MACHINE_MODE"):
            self.basic_instr.append(self.instr_category["CSR"])
        if(cfg.no_wfi == 0):
            self.basic_instr.append("WFI")

    def create_csr_filter(self, cfg):
        self.include_reg.clear()
        self.exclude_reg.clear()

        if(cfg.enable_illegal_csr_instruction):
            self.exclude_reg = self.implemented_csr
        elif(cfg.enable_access_invalid_csr_level):
            self.include_reg = cfg.invalid_priv_mode_csrs
        else:
            if(cfg.init_privileged_mode == "MACHINE_MODE"):    # Machine Mode
                self.include_reg.append("MSCRATCH")
            elif(cfg.init_privileged_mode == "SUPERVISOR_MODE"):  # Supervisor Mode
                self.include_reg.append("SSCRATCH")
            else:                                              # User Mode
                self.include_reg.append("USCRATCH")

    def get_rand_instr(self, include_instr=[], exclude_instr=[],
                       include_category=[], exclude_category=[],
                       include_group=[], exclude_group=[]):
        idx = BitArray(uint = 0, length = 32)
        name = ""
        allowed_instr = []
        disallowed_instr = []
        # allowed_categories = []

        for items in include_category:
            allowed_instr.append(self.instr_category[items])

        for items in exclude_category:
            if(items in self.instr_category):
                disallowed_instr.append(self.instr_category[items])
        for items in include_group:
            allowed_instr.append(self.instr_group[items])
        for items in exclude_group:
            if(items in self.instr_group):
                disallowed_instr.append(self.instr_group[items])

        disallowed_instr.extend(exclude_instr)

        if(len(disallowed_instr) == 0):
            if(len(include_instr) > 0):
                idx = random.randrange(0, len(include_instr) - 1)
                name = include_instr[idx]
            elif(len(allowed_instr > 0)):
                idx = random.randrange(0, len(allowed_instr) - 1)
                name = allowed_instr[idx]
            else:
                idx = random.randrange(0, len(self.instr_names) - 1)
                name = self.instr_names[idx]
        else:
            # TODO
            instr_names_set = set(self.instr_names)
            disallowed_instr_set = set(disallowed_instr)
            allowed_instr_set = set(allowed_instr)
            include_instr_set = set(include_instr)
            excluded_instr_names_list = list(instr_names_set - disallowed_instr_set)
            excluded_allowed_instr_list = list(allowed_instr_set - disallowed_instr_set)
            include_instr_list = list(include_instr_set - disallowed_instr_set)

            name = random.choice(excluded_instr_names_list)
            if(len(include_instr) > 0):
                name = random.choice(include_instr_list)
            if(len(allowed_instr) > 0):
                name = random.choice(excluded_allowed_instr_list)
            if(name is None):
                logging.critical("%s Cannot generate random instruction", riscv_instr.__name__)
                sys.exit(1)

        instr_h = copy(self.instr_template[name])
        return instr_h

    def get_load_store_instr(self, load_store_instr):
        instr_h = riscv_instr()
        if(len(load_store_instr) == 0):
            load_store_instr = self.instr_category["LOAD"] + \
                self.instr_category["STORE"]
        self.idx = random.randrange(0, len(load_store_instr) - 1)
        name = load_store_instr[self.idx]
        instr_h = copy(self.instr_template[name])
        return instr_h

    def get_instr(self, name):
        if (not self.instr_template.get(name)):
            logging.critical("Cannot get instr %s", name)
        instr_h = copy(self.instr_template[name])
        return instr_h

    def set_rand_mode(self):
        # rand_mode setting for Instruction Format
        if(self.format.name == "R_FORMAT"):
            self.has_imm = 0
        if(self.format.name == "I_FORMAT"):
            self.has_rs2 = 0
        if(self.format.name in ["S_FORMAT", "B_FORMAT"]):
            self.has_rd = 0
        if(self.format.name in ["U_FORMAT", "J_FORMAT"]):
            self.has_rs1 = 0
            self.has_rs2 = 0

        # rand_mode setting for Instruction Category
        if(self.category.name == "CSR"):
            self.has_rs2 = 0
            if(self.format.name == "I_FORMAT"):
                self.has_rs1 = 0

    def pre_randomize(self):
        pass  # TODO

    def set_imm_len(self):
        if(self.format.name in ["U_FORMAT", "J_FORMAT"]):
            self.imm_len = 20
        elif(self.format.name in ["I_FORMAT", "S_FORMAT", "B_FORMAT"]):
            if(self.imm_type.name == "UIMM"):
                self.imm_len = 5
            else:
                self.imm_len = 11
        self.imm_mask = self.imm_mask << self.imm_len

    def extend_imm(self):
        sign = 0
        self.imm = self.imm << (32 - self.imm_len)
        # sign = imm[31]
        sign = self.imm.bin[0:1:1]
        self.imm = self.imm >> (32 - self.imm_len)
        # Signed extension
        if((sign and not(self.format == "U_FORMAT")) or (self.imm_type in ["UIMM", "NZUIMM"])):
            self.imm = self.imm_mask | self.imm

    def post_randomize(self):
        self.extend_imm()
        self.update_imm_str()

    def convert2asm(self):
        pass

    def get_opcode(self):
        if(self.instr_name.name == "LUI"):
            return (BitArray(uint = 55, length = 7).bin)
        elif(self.instr_name.name == "AUIPC"):
            return (BitArray(uint = 23, length = 7).bin)
        elif(self.instr_name.name == "JAL"):
            return (BitArray(uint = 23, length = 7).bin)
        elif(self.instr_name.name == "JALR"):
            return (BitArray(uint = 111, length = 7).bin)
        elif(self.instr_name.name in ["BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU"]):
            return (BitArray(uint = 103, length = 7).bin)
        elif(self.instr_name.name in ["LB", "LH", "LW", "LBU", "LHU", "LWU", "LD"]):
            return (BitArray(uint = 99, length = 7).bin)
        elif(self.instr_name.name in ["SB", "SH", "SW", "SD"]):
            return (BitArray(uint = 35, length = 7).bin)
        elif(self.instr_name.name in ["ADDI", "SLTI", "SLTIU", "XORI", "ORI", "ANDI",
                                      "SLLI", "SRLI", "SRAI", "NOP"]):
            return (BitArray(uint = 19, length = 7).bin)
        elif(self.instr_name.name in ["ADD", "SUB", "SLL", "SLT", "SLTU", "XOR", "SRL",
                                      "SRA", "OR", "AND", "MUL", "MULH", "MULHSU", "MULHU",
                                      "DIV", "DIVU", "REM", "REMU"]):
            return (BitArray(uint = 51, length = 7).bin)
        elif(self.instr_name.name in ["ADDIW", "SLLIW", "SRLIW", "SRAIW"]):
            return (BitArray(uint = 27, length = 7).bin)
        elif(self.instr_name.name in ["MULH", "MULHSU", "MULHU", "DIV", "DIVU", "REM", "REMU"]):
            return (BitArray(uint = 51, length = 7).bin)
        elif(self.instr_name.name in ["FENCE", "FENCE_I"]):
            return (BitArray(uint = 15, length = 7).bin)
        elif(self.instr_name.name in ["ECALL", "EBREAK", "CSRRW", "CSRRS", "CSRRC", "CSRRWI",
                                      "CSRRSI", "CSRRCI"]):
            return (BitArray(uint = 115, length = 7).bin)
        elif(self.instr_name.name in ["ADDW", "SUBW", "SLLW", "SRLW", "SRAW", "MULW", "DIVW",
                                      "DIVUW", "REMW", "REMUW"]):
            return (BitArray(uint = 59, length = 7).bin)
        elif(self.instr_name.name in ["ECALL", "EBREAK", "URET", "SRET", "MRET", "DRET", "WFI",
                                      "SFENCE_VMA"]):
            return (BitArray(uint = 115, length = 7).bin)
        else:
            logging.critical("Unsupported instruction %0s", self.instr_name.name)
            sys.exit(1)

    def get_func3(self):
        if(self.instr_name.name in ["JALR", "BEQ", "LB", "SB", "ADDI", "NOP", "ADD", "SUB",
                                    "FENCE", "ECALL", "EBREAK", "ADDIW", "ADDW", "SUBW", "MUL",
                                    "MULW", "ECALL", "EBREAK", "URET", "SRET", "MRET", "DRET",
                                    "WFI", "SFENCE_VMA"]):
            return (BitArray(uint = 0, length = 3).bin)
        elif(self.instr_name.name in ["BNE", "LH", "SH", "SLLI", "SLL", "FENCE_I", "CSRRW", "SLLIW",
                                      "SLLW", "MULH"]):
            return (BitArray(uint = 1, length = 3).bin)
        elif(self.instr_name.name in ["LW", "SW", "SLTI", "SLT", "CSRRS", "MULHS"]):
            return (BitArray(uint = 2, length = 3).bin)
        elif(self.instr_name.name in ["SLTIU", "SLTU", "CSRRC", "LD", "SD", "MULHU"]):
            return (BitArray(uint = 3, length = 3).bin)
        elif(self.instr_name.name in ["BLT", "LBU", "XORI", "XOR", "DIV", "DIVW"]):
            return (BitArray(uint = 4, length = 3).bin)
        elif(self.instr_name.name in ["BGE", "LHU", "SRLI", "SRAI", "SRL", "SRA", "CSRRWI", "SRLIW",
                                      "SRAIW", "SRLW",
                                      "SRAW", "DIVU", "DIVUW"]):
            return (BitArray(uint = 5, length = 3).bin)
        elif(self.instr_name.name in ["BLTU", "ORI", "OR", "CSRRSI", "LWU", "REM", "REMW"]):
            return (BitArray(uint = 6, length = 3).bin)
        elif(self.instr_name.name in ["BGEU", "ANDI", "AND", "CSRRCI", "REMU", "REMUW"]):
            return (BitArray(uint = 7, length = 3).bin)
        else:
            logging.critical("Unsupported instruction %0s", self.instr_name.name)
            sys.exit(1)

    def get_func7(self):
        if(self.instr_name.name in ["SLLI", "SRLI", "ADD", "SLL", "SLT", "SLTU", "XOR",
                                    "SRL", "OR", "AND", "FENCE", "FENCE_I", "SLLIW",
                                    "SRLIW", "ADDW", "SLLW", "SRLW", "ECALL", "EBREAK", "URET"]):
            return (BitArray(uint = 0, length = 7).bin)
        elif(self.instr_name.name in ["SUB", "SRA", "SRAIW", "SUBW", "SRAW"]):
            return (BitArray(uint = 32, length = 7).bin)
        elif(self.instr_name.name in ["MUL", "MULH", "MULHSU", "MULHU", "DIV", "DIVU", "REM",
                                      "REMU", "MULW", "DIVW", "DIVUW", "REMW", "REMUW"]):
            return (BitArray(uint = 1, length = 7).bin)
        elif(self.instr_name.name in ["SRET", "WFI"]):
            return (BitArray(uint = 8, length = 7).bin)
        elif(self.instr_name.name == "MRET"):
            return (BitArray(uint = 24, length = 7).bin)
        elif(self.instr_name.name == "DRET"):
            return (BitArray(uint = 61, length = 7).bin)
        elif(self.instr_name.name == "SFENCE_VMA"):
            return (BitArray(uint = 9, length = 7).bin)
        else:
            logging.critical("Unsupported instruction %0s", self.instr_name.name)
            sys.exit(1)

    def convert2bin(self):
        pass  # TODO

    def get_instr_name(self):
        get_instr_name = self.instr_name.name
        for i in get_instr_name:
            if(i == "_"):
                get_instr_name = get_instr_name.replace(i, ".")
        return get_instr_name

    def get_c_gpr(self, gpr):
        return self.gpr

    def get_imm(self):
        return self.imm_str

    def clear_unused_label(self):
        if(self.has_label and not(self.is_branch_target) and self.is_local_numeric_label):
            self.has_label = 0

    def do_copy(self):
        pass  # TODO

    def update_imm_str(self):
        self.imm_str = str(self.imm)


riscv_instr_ins = riscv_instr()
cfg = riscv_instr_gen_config()
