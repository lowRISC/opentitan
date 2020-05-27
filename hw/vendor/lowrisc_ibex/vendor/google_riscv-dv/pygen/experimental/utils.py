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

Parse the regression testlist in YAML format
"""

# importing enum for enumerations
import enum
import random
from bitstring import BitArray, BitStream

# Enumerationa
# Privileged mode: only machine mode for now
# class privileged_mode_t(enum.Enum):
#     MACHINE_MODE = 1
privileged_mode_t = ["MACHINE_MODE"]

# Type of the immediate
# class imm_t(enum.Enum):
#     IMM = 1  # Sign Immediate
#     UIMM = 2  # Unsigned Immediate
#     NZUIMM = 3  # Non-zero Unsigned Immediate
#     NZIMM = 4  # Non-zero Signed Immediate
imm_t = ["IMM", "UIMM", "NZUIMM", "NZIMM"]
# riscv extensions? only RV32I for now
# class riscv_instr_group_t(enum.Enum):
#     RV32I = 1
riscv_instr_group_t = ["RV32I"]

# riscv instruction category
# class riscv_instr_category_t(enum.Enum):
#     LOAD = 1
#     STORE = 2
#     SHIFT = 3
#     ARITHMETIC = 4
#     LOGICAL = 5
#     COMPARE = 6
#     BRANCH = 7
#     JUMP = 8
#     SYNCH = 9
#     SYSTEM = 10
#     COUNTER = 11
#     CSR = 12
#     CHANGELEVEL = 13
#     TRAP = 14
#     INTERRUPT = 15
riscv_instr_category_t = [
    "LOAD", "STORE", "SHIFT", "ARITHMETIC", "LOGICAL", "COMPARE", "BRANCH",
    "JUMP", "SYNCH", "SYSTEM", "COUNTER", "CSR", "CHANGELEVEL", "TRAP",
    "INTERRUPT"
]
# riscv instruction format, RV32I has only 6 different instruction types
# class riscv_instr_format_t(enum.Enum):
#     J_FORMAT = 1
#     U_FORMAT = 2
#     I_FORMAT = 3
#     B_FORMAT = 4
#     R_FORMAT = 5
#     S_FORMAT = 6
riscv_instr_format_t = [
    "J_FORMAT", "U_FORMAT", "I_FORMAT", "B_FORMAT", "R_FORMAT", "S_FORMAT"
]

# Existing instructions in RV32I
# class riscv_instr_name_t(enum.Enum):
#     LUI = 1
#     AUIPC = 2
#     JAL = 3
#     JALR = 4
#     BEQ = 5
#     BNE = 6
#     BLT = 7
#     BGE = 8
#     BLTU = 9
#     BGEU = 10
#     LB = 11
#     LH = 12
#     LW = 13
#     LBU = 14
#     LHU = 15
#     SB = 16
#     SH = 17
#     SW = 18
#     ADDI = 19
#     SLTI = 20
#     SLTIU = 21
#     XORI = 22
#     ORI = 23
#     ANDI = 24
#     SLLI = 25
#     SRLI = 26
#     SRAI = 27
#     ADD = 28
#     SUB = 29
#     SLL = 30
#     SLT = 31
#     SLTU = 32
#     XOR = 33
#     SRL = 34
#     SRA = 35
#     OR = 36
#     AND = 37
#     NOP = 38
#     FENCE = 39
#     FENCEI = 40
#     ECALL = 41
#     EBREAK = 42
#     CSRRW = 43
#     CSRRS = 44
#     CSRRC = 45
#     CSRRWI = 46
#     CSRRSI = 47
#     CSRRCI = 48
riscv_instr_name_t = [
    "LUI", "AUIPC", "JAL", "JALR", "BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU",
    "LB", "LH", "LW", "LBU", "LHU", "SB", "SH", "SW", "ADDI", "SLTI", "SLTIU",
    "XORI", "ORI", "ANDI", "SLLI", "SRLI", "SRAI", "ADD", "SUB", "SLL", "SLT",
    "SLTU", "XOR", "SRL", "SRA", "OR", "AND", "NOP", "FENCE", "FENCEI", "ECALL",
    "EBREAK", "CSRRW", "CSRRS", "CSRRC", "CSRRWI", "CSRRSI", "CSRRCI"
]
# class riscv_reg_t(enum.Enum):
#     ZERO = 0
#     RA = 1
#     SP = 2
#     GP = 3
#     TP = 4
#     T0 = 5
#     T1 = 6
#     T2 = 7
#     S0 = 8
#     S1 = 9
#     A0 = 10
#     A1 = 11
#     A2 = 12
#     A3 = 13
#     A4 = 14
#     A5 = 15
#     A6 = 16
#     A7 = 17
#     S2 = 18
#     S3 = 19
#     S4 = 20
#     S5 = 21
#     S6 = 22
#     S7 = 23
#     S8 = 24
#     S9 = 25
#     S10 = 26
#     S11 = 27
#     T3 = 28
#     T4 = 29
#     T5 = 30
#     T6 = 31
riscv_pseudo_instr_name_t = ["LI", "LA"]
riscv_reg_t = [
    "ZERO", "RA", "SP", "GP", "TP", "T0", "T1", "T2", "S0", "S1", "A0", "A1",
    "A2", "A3", "A4", "A5", "A6", "A7", "S2", "S3", "S4", "S5", "S6", "S7",
    "S8", "S9", "S10", "S11", "T3", "T4", "T5", "T6"
]

# data_pattern_t = ["RAND_DATA",
#                   "ALL_ZERO",
#                   "INCR_VAL"]
data_pattern_t = ["RAND_DATA", "INCR_VAL"]


def format_data(data, byte_per_group=4):
  temp_str = "0x"
  for i in range(len(data)):
    if (i % byte_per_group == 0) and (i != len(data) - 1) and (i != 0):
      temp_str = temp_str + ", 0x"
    # to avoid 0x, I added [2:]
    temp_str = temp_str + str(data[i])[2:]
  return temp_str


XLEN = 32
length = 18
indent = "{:18s}".format(" ")
inden = "{:12s}".format(" ")
data_page_size = 4096
num_of_data_pages = 40
