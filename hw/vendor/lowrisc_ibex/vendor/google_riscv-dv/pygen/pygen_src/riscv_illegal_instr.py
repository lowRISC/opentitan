
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
import logging
from enum import IntEnum, auto
from importlib import import_module
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_instr_pkg import riscv_instr_group_t
rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")


# ---------------------------------------------------------------------------------------------
# This class is used to generate illegal or HINT instructions.
# The illegal instruction will be generated in binary format and mixed with other valid instr.
# The mixed instruction stream will be stored in data section and loaded to instruction pages
# at run time.
# ---------------------------------------------------------------------------------------------


class illegal_instr_type_e(IntEnum):
    kIllegalOpcode = 0
    kIllegalCompressedOpcode = auto()
    kIllegalFunc3 = auto()
    kIllegalFunc7 = auto()
    kReservedCompressedInstr = auto()
    kHintInstr = auto()
    kIllegalSystemInstr = auto()


class reserved_c_instr_e(IntEnum):
    kIllegalCompressed = 0
    kReservedAddispn = auto()
    kReservedAddiw = auto()
    kReservedAddi16sp = auto()
    kReservedLui = auto()
    kReservedLwsp = auto()
    kReservedLdsp = auto()
    kReservedLqsp = auto()
    kReservedJr = auto()
    kReservedC0 = auto()
    kReservedC1 = auto()
    kReservedC2 = auto()


@vsc.randobj
class riscv_illegal_instr:
    def __init__(self):
        self.comment = ""
        self.exception = vsc.rand_enum_t(illegal_instr_type_e)
        self.reserved_c = vsc.rand_enum_t(reserved_c_instr_e)
        self.instr_bin = vsc.rand_bit_t(32)
        self.opcode = vsc.rand_bit_t(7)
        self.compressed = vsc.rand_bit_t(1)
        self.func3 = vsc.rand_bit_t(3)
        self.func7 = vsc.rand_bit_t(7)
        self.has_func3 = vsc.rand_bit_t(1)
        self.has_func7 = vsc.rand_bit_t(1)
        self.c_op = vsc.rand_bit_t(2)
        self.c_msb = vsc.rand_bit_t(3)
        self.csrs = []
        # Default legal self.opcode for RV32I instructions
        self.legal_opcode = vsc.list_t(vsc.bit_t(7))
        self.legal_opcode = [3, 15, 19, 23, 35, 55, 99, 51, 103, 115, 111]
        # Default legal self.opcode for RV32C instructions
        self.legal_c00_opcode = vsc.list_t(vsc.bit_t(3))
        self.legal_c00_opcode = [0, 2, 6]
        self.legal_c10_opcode = vsc.list_t(vsc.bit_t(3))
        self.legal_c10_opcode = [0, 2, 4, 6]
        self.xlen = vsc.uint8_t(0)
        self.xlen = rcs.XLEN
        self.temp_1 = vsc.bit_t(6)

    @vsc.constraint
    def exception_dist_c(self):
        vsc.dist(self.exception,
                 [vsc.weight(illegal_instr_type_e.kIllegalOpcode, 3),
                  vsc.weight(illegal_instr_type_e.kIllegalCompressedOpcode, 1),
                  vsc.weight(illegal_instr_type_e.kIllegalFunc3, 1),
                  vsc.weight(illegal_instr_type_e.kIllegalFunc7, 1),
                  vsc.weight(illegal_instr_type_e.kReservedCompressedInstr, 1),
                  vsc.weight(illegal_instr_type_e.kHintInstr, 3),
                  vsc.weight(illegal_instr_type_e.kIllegalSystemInstr, 3)
                  ])

    @vsc.constraint
    def instr_bit_assignment_c(self):
        vsc.solve_order(self.opcode, self.instr_bin)
        vsc.solve_order(self.func3, self.instr_bin)
        vsc.solve_order(self.func7, self.instr_bin)
        vsc.solve_order(self.c_msb, self.instr_bin)
        # vsc.solve_order(self.c_op, self.instr_bin)
        with vsc.if_then(self.compressed == 1):
            self.instr_bin[1:0] == self.c_op
            self.instr_bin[15:13] == self.c_msb
        with vsc.else_then():
            self.instr_bin[6:0] == self.opcode
            with vsc.if_then(self.has_func7 == 1):
                self.instr_bin[31:25] == self.func7
            with vsc.if_then(self.has_func3 == 1):
                self.instr_bin[14:12] == self.func3

    # Invalid SYSTEM instructions
    @vsc.constraint
    def system_instr_c(self):
        with vsc.if_then(self.exception == illegal_instr_type_e.kIllegalSystemInstr):
            self.opcode == 115
            # ECALL/EBREAK/xRET/WFI
            with vsc.if_then(self.func3 == 0):
                # Constrain RS1 and RD to be non-zero
                self.instr_bin[19:15] != 0
                self.instr_bin[11:7] != 0
                # Valid SYSTEM instructions considered by this
                # Constrain the upper 12 bits to be invalid
                self.instr_bin[31:20].not_inside(vsc.rangelist(0, 1, 2, 258, 770, 1970, 261))
            with vsc.else_then():
                # Invalid CSR instructions
                self.instr_bin[31:20].not_inside(vsc.rangelist(self.csrs))
                # self.instr_bin[20:31].not_inside(vsc.rangelist(self.custom_csr))

    @vsc.constraint
    def legal_rv32_c_slli(self):
        with vsc.if_then((self.c_msb == 0) and (self.c_op == 2) and (self.xlen == 32)):
            with vsc.if_then(self.exception == illegal_instr_type_e.kReservedCompressedInstr):
                self.instr_bin[12] == 1
            with vsc.else_then():
                self.instr_bin[12] == 0

    @vsc.constraint
    def exception_type_c(self):
        with vsc.if_then(self.compressed == 1):
            self.exception.inside(vsc.rangelist(illegal_instr_type_e.kReservedCompressedInstr,
                                                illegal_instr_type_e.kIllegalCompressedOpcode,
                                                illegal_instr_type_e.kHintInstr))
        with vsc.else_then():
            self.exception.inside(vsc.rangelist(illegal_instr_type_e.kIllegalOpcode,
                                                illegal_instr_type_e.kIllegalFunc3,
                                                illegal_instr_type_e.kIllegalFunc7,
                                                illegal_instr_type_e.kIllegalSystemInstr))
        with vsc.if_then(self.has_func7 == 0):
            self.exception != illegal_instr_type_e.kIllegalFunc7
        with vsc.if_then(self.has_func3 == 0):
            self.exception != illegal_instr_type_e.kIllegalFunc3

    @vsc.constraint
    def compressed_instr_op_c(self):
        self.c_op != 3

    # Avoid generating illegal func3/func7 errors for self.opcode used by B-extension for now
    # TODO: add support for generating illegal B-extension instructions
    @vsc.constraint
    def b_extension_c(self):
        if riscv_instr_group_t.RV32B in rcs.supported_isa:
            with vsc.if_then(self.exception in [illegal_instr_type_e.kIllegalFunc3,
                                                illegal_instr_type_e.kIllegalFunc7]):
                self.opcode.inside(vsc.rangelist([51, 19, 59]))

    @vsc.constraint
    def illegal_compressed_op_c(self):
        with vsc.if_then(self.exception == illegal_instr_type_e.kIllegalCompressedOpcode):
            self.c_op != 1
            with vsc.if_then(self.legal_c00_opcode.size == 8):
                self.c_op != 0
            with vsc.else_then():
                self.c_msb.not_inside(vsc.rangelist(self.legal_c00_opcode))
            with vsc.if_then(self.legal_c10_opcode.size == 8):
                self.c_op != 2
            with vsc.else_then():
                self.c_msb.not_inside(vsc.rangelist(self.legal_c10_opcode))

    @vsc.constraint
    def reserved_compressed_instr_c(self):
        vsc.solve_order(self.exception, self.reserved_c)
        vsc.solve_order(self.exception, self.opcode)
        vsc.solve_order(self.reserved_c, self.instr_bin)
        vsc.solve_order(self.reserved_c, self.c_msb)
        vsc.solve_order(self.reserved_c, self.c_op)
        with vsc.if_then(self.xlen == 32):
            # c.addiw is RV64/RV128 only instruction, the encoding is used for C.JAL for RV32C
            self.reserved_c != reserved_c_instr_e.kReservedAddiw
        with vsc.if_then(self.exception == illegal_instr_type_e.kReservedCompressedInstr):
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kIllegalCompressed):
                self.instr_bin[15:0] == 0
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedAddispn):
                ((self.instr_bin[15:0] == 0) and (self.c_op == 0))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedAddiw):
                ((self.c_msb == 1) and (self.c_op == 1) and
                 (self.instr_bin[11:7] == 0))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedC0):
                ((self.instr_bin[15:10] == 39) and
                 (self.instr_bin[6:5] == 2) and (self.c_op == 1))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedC1):
                ((self.instr_bin[15:10] == 39) and
                 (self.instr_bin[6:5] == 3) and (self.c_op == 1))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedC2):
                ((self.c_msb == 4) and (self.c_op == 0))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedAddi16sp):
                ((self.c_msb == 3) and (self.c_op == 1) and
                 (self.instr_bin[11:7] == 2) and
                 (not self.instr_bin[12]) and (self.instr_bin[6:2] == 0))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedLui):
                ((self.c_msb == 3) and (self.c_op == 1) and
                 (not self.instr_bin[12]) and (self.instr_bin[6:2] == 0))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedJr):
                self.instr_bin == 32770
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedLqsp):
                ((self.c_msb == 1) and (self.c_op == 2) and
                 (self.instr_bin[11:7] == 0))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedLwsp):
                ((self.c_msb == 2) and (self.c_op == 2) and
                 (self.instr_bin[11:7] == 0))
            with vsc.if_then(self.reserved_c == reserved_c_instr_e.kReservedLdsp):
                ((self.c_msb == 3) and (self.c_op == 2) and (self.instr_bin[11:7] == 0))

    @vsc.constraint
    def hint_instr_c(self):
        with vsc.if_then(self.exception == illegal_instr_type_e.kHintInstr):
            ((self.c_msb == 0) and (self.c_op == 1) and (self.instr_bin[12] +
                                                         self.instr_bin[6:2] == 0)) or \
                ((self.c_msb == 2) and (self.c_op == 1) and (self.instr_bin[11:7] == 0)) or \
                ((self.c_msb == 4) and (self.c_op == 1) and (self.instr_bin[12:11] == 0) and
                 (self.instr_bin[6:2] == 0)) or \
                ((self.c_msb == 4) and (self.c_op == 2) and (self.instr_bin[11:7] == 0) and
                 (self.instr_bin[6:2] != 0)) or \
                ((self.c_msb == 3) and (self.c_op == 1) and (self.instr_bin[11:7] == 0) and
                 (self.instr_bin[12] + self.instr_bin[6:2]) != 0) or \
                ((self.c_msb == 0) and (self.c_op == 2) and (self.instr_bin[11:7] == 0)) or \
                ((self.c_msb == 0) and (self.c_op == 2) and (self.instr_bin[11:7] != 0) and
                 not(self.instr_bin[12]) and (self.instr_bin[6:2] == 0)) or \
                ((self.c_msb == 4) and (self.c_op == 2) and (self.instr_bin[11:7] == 0) and
                 self.instr_bin[12] and (self.instr_bin[6:2] != 0))

    @vsc.constraint
    def illegal_opcode_c(self):
        vsc.solve_order(self.opcode, self.instr_bin)
        with vsc.if_then(self.exception == illegal_instr_type_e.kIllegalOpcode):
            self.opcode.not_inside(vsc.rangelist(self.legal_opcode))
            self.opcode[1:0] == 3
        with vsc.else_then():
            self.opcode.inside(vsc.rangelist(self.legal_opcode))

    # TODO: Enable atomic instruction
    @vsc.constraint
    def no_atomic_c(self):
        with vsc.if_then(self.exception != illegal_instr_type_e.kIllegalOpcode):
            self.opcode != 47

    @vsc.constraint
    def illegal_func3_c(self):
        vsc.solve_order(self.opcode, self.func3)
        with vsc.if_then(self.compressed == 0):
            with vsc.if_then(self.exception == illegal_instr_type_e.kIllegalFunc3):
                with vsc.if_then(self.opcode == 103):
                    self.func3 != 0
                with vsc.if_then(self.opcode == 99):
                    self.func3.inside(vsc.rangelist(2, 3))
                with vsc.if_then(self.xlen == 32):
                    with vsc.if_then(self.opcode == 35):
                        self.func3 >= 3
                    with vsc.if_then(self.opcode == 3):
                        self.func3.inside(vsc.rangelist(3, 7))
                with vsc.else_then():
                    with vsc.if_then(self.opcode == 35):
                        self.func3 > 3
                    with vsc.if_then(self.opcode == 3):
                        self.func3 == 7
                with vsc.if_then(self.opcode == 15):
                    self.func3.not_inside(vsc.rangelist(0, 1))
                with vsc.if_then(self.opcode == 115):
                    self.func3 == 4
                with vsc.if_then(self.opcode == 27):
                    self.func3.not_inside(vsc.rangelist(0, 1, 5))
                with vsc.if_then(self.opcode == 59):
                    self.func3.inside(vsc.rangelist(2, 3))
                self.opcode.inside(vsc.rangelist(103, 99, 3, 35, 15, 115, 27, 59))
            with vsc.else_then():
                with vsc.if_then(self.opcode == 103):
                    self.func3 == 0
                with vsc.if_then(self.opcode == 99):
                    self.func3.inside(vsc.rangelist(2, 3))
                with vsc.if_then(self.xlen == 32):
                    with vsc.if_then(self.opcode == 35):
                        self.func3 < 3
                    with vsc.if_then(self.opcode == 3):
                        self.func3.inside(vsc.rangelist(3, 7))
                with vsc.else_then():
                    with vsc.if_then(self.opcode == 35):
                        self.func3 <= 3
                    with vsc.if_then(self.opcode == 3):
                        self.func3 != 7
                with vsc.if_then(self.opcode == 15):
                    self.func3.inside(vsc.rangelist(0, 1))
                with vsc.if_then(self.opcode == 115):
                    self.func3 != 4
                with vsc.if_then(self.opcode == 27):
                    self.func3.inside(vsc.rangelist(0, 1, 5))
                with vsc.if_then(self.opcode == 59):
                    self.func3.not_inside(vsc.rangelist(2, 3))

    @vsc.constraint
    def has_func7_c(self):
        vsc.solve_order(self.opcode, self.func7)
        with vsc.if_then((self.opcode == 19) and (self.func3 == 1 or self.func3 == 5) or
                         (self.opcode == 51 or self.opcode == 59)):
            self.has_func7 == 1
        with vsc.else_then():
            self.has_func7 == 0

    @vsc.constraint
    def has_func3_c(self):
        vsc.solve_order(self.opcode, self.func7)
        with vsc.if_then(self.opcode == 55 or self.opcode == 111 or self.opcode == 23):
            self.has_func3 == 0
        with vsc.else_then():
            self.has_func3 == 1

    @vsc.constraint
    def illegal_func7_c(self):
        with vsc.if_then(self.compressed == 0):
            with vsc.if_then(self.exception == illegal_instr_type_e.kIllegalFunc7):
                self.func7.not_inside(vsc.rangelist(0, 32, 1))
                with vsc.if_then(self.opcode == 9):  # SLLI, SRLI, SRAI
                    self.func7[6:1].not_inside(vsc.rangelist(0, 16))
            with vsc.else_then():
                self.func7.inside(vsc.rangelist(0, 32, 1))

    def initialize(self):
        if (riscv_instr_group_t.RV32F in rcs.supported_isa) or \
                (riscv_instr_group_t.RV32D in rcs.supported_isa):
            self.legal_opcode.extend(7, 39, 67, 71, 75, 79, 83)
        if riscv_instr_group_t.RV64I in rcs.supported_isa:
            self.legal_opcode.append(27)
        if riscv_instr_group_t.RV32A in rcs.supported_isa:
            self.legal_opcode.append(47)
        if (riscv_instr_group_t.RV64I in rcs.supported_isa) or \
                (riscv_instr_group_t.RV64M in rcs.supported_isa):
            self.legal_opcode.append(59)
        if riscv_instr_group_t.RV64I in rcs.supported_isa:
            self.legal_c00_opcode.extend(3, 7)
            self.legal_c10_opcode.extend(3, 7)
        # TODO csr

    def get_bin_str(self):
        if self.compressed == 1:
            local_instr_bin = self.instr_bin & 0xffff
        else:
            local_instr_bin = hex(self.instr_bin)
        logging.info("Illegal instruction type: {}, illegal instruction: {}".format(
            self.exception.name, local_instr_bin))
        return ("{}".format(local_instr_bin))

    def post_randomize(self):
        self.comment = self.exception.name
        if self.exception == illegal_instr_type_e.kReservedCompressedInstr:
            self.comment += " {}".format(self.reserved_c.name)
        elif self.exception == illegal_instr_type_e.kIllegalOpcode:
            self.comment += " {}".format(self.opcode)
