// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_tracer_pkg;
import ibex_pkg::*;

parameter logic [1:0] OPCODE_C0 = 2'b00;
parameter logic [1:0] OPCODE_C1 = 2'b01;
parameter logic [1:0] OPCODE_C2 = 2'b10;

// instruction masks (for tracer)
parameter logic [31:0] INSN_LUI     = { 25'h?,                           {OPCODE_LUI  } };
parameter logic [31:0] INSN_AUIPC   = { 25'h?,                           {OPCODE_AUIPC} };
parameter logic [31:0] INSN_JAL     = { 25'h?,                           {OPCODE_JAL  } };
parameter logic [31:0] INSN_JALR    = { 17'h?,             3'b000, 5'h?, {OPCODE_JALR } };

// BRANCH
parameter logic [31:0] INSN_BEQ     = { 17'h?,             3'b000, 5'h?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BNE     = { 17'h?,             3'b001, 5'h?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BLT     = { 17'h?,             3'b100, 5'h?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BGE     = { 17'h?,             3'b101, 5'h?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BLTU    = { 17'h?,             3'b110, 5'h?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BGEU    = { 17'h?,             3'b111, 5'h?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BALL    = { 17'h?,             3'b010, 5'h?, {OPCODE_BRANCH} };

// OPIMM
parameter logic [31:0] INSN_ADDI    = { 17'h?,             3'b000, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SLTI    = { 17'h?,             3'b010, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SLTIU   = { 17'h?,             3'b011, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_XORI    = { 17'h?,             3'b100, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORI     = { 17'h?,             3'b110, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ANDI    = { 17'h?,             3'b111, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SLLI    = { 7'b0000000, 10'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SRLI    = { 7'b0000000, 10'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SRAI    = { 7'b0100000, 10'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

// OP
parameter logic [31:0] INSN_ADD     = { 7'b0000000, 10'h?, 3'b000, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SUB     = { 7'b0100000, 10'h?, 3'b000, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SLL     = { 7'b0000000, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SLT     = { 7'b0000000, 10'h?, 3'b010, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SLTU    = { 7'b0000000, 10'h?, 3'b011, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_XOR     = { 7'b0000000, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SRL     = { 7'b0000000, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SRA     = { 7'b0100000, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_OR      = { 7'b0000000, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_AND     = { 7'b0000000, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };

// SYSTEM
parameter logic [31:0] INSN_CSRRW   = { 17'h?,             3'b001, 5'h?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRS   = { 17'h?,             3'b010, 5'h?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRC   = { 17'h?,             3'b011, 5'h?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRWI  = { 17'h?,             3'b101, 5'h?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRSI  = { 17'h?,             3'b110, 5'h?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRCI  = { 17'h?,             3'b111, 5'h?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_ECALL   = { 12'b000000000000,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_EBREAK  = { 12'b000000000001,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_MRET    = { 12'b001100000010,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_DRET    = { 12'b011110110010,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_WFI     = { 12'b000100000101,         13'b0, {OPCODE_SYSTEM} };

// RV32M
parameter logic [31:0] INSN_DIV     = { 7'b0000001, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_DIVU    = { 7'b0000001, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_REM     = { 7'b0000001, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_REMU    = { 7'b0000001, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_PMUL    = { 7'b0000001, 10'h?, 3'b000, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_PMUH    = { 7'b0000001, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_PMULHSU = { 7'b0000001, 10'h?, 3'b010, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_PMULHU  = { 7'b0000001, 10'h?, 3'b011, 5'h?, {OPCODE_OP} };

// RV32B
// ZBB
parameter logic [31:0] INSN_SLOI = { 5'b00100        , 12'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SROI = { 5'b00100        , 12'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_RORI = { 5'b01100        , 12'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_CLZ  = { 12'b011000000000, 5'h?,  3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_CTZ  = { 12'b011000000001, 5'h?,  3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_PCNT = { 12'b011000000010, 5'h?,  3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SEXTB = { 12'b011000000100, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SEXTH = { 12'b011000000101, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
// sext -- pseudoinstruction: andi rd, rs 255
parameter logic [31:0] INSN_ZEXTB = { 4'b0000, 8'b11111111, 5'h?, 3'b111, 5'h?, {OPCODE_OP_IMM} };
// sext -- pseudoinstruction: pack rd, rs zero
parameter logic [31:0] INSN_ZEXTH = { 7'b0000100, 5'b00000, 5'h?, 3'b100, 5'h?, {OPCODE_OP} };

parameter logic [31:0] INSN_SLO   = { 7'b0010000, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SRO   = { 7'b0010000, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_ROL   = { 7'b0110000, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_ROR   = { 7'b0110000, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_MIN   = { 7'b0000101, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_MAX   = { 7'b0000101, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_MINU  = { 7'b0000101, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_MAXU  = { 7'b0000101, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_XNOR  = { 7'b0100000, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_ORN   = { 7'b0100000, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_ANDN  = { 7'b0100000, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_PACK  = { 7'b0000100, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_PACKU = { 7'b0100100, 10'h?, 3'b100, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_PACKH = { 7'b0000100, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };

// ZBS
parameter logic [31:0] INSN_SBCLRI = { 5'b01001, 12'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SBSETI = { 5'b00101, 12'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SBINVI = { 5'b01101, 12'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SBEXTI = { 5'b01001, 12'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

parameter logic [31:0] INSN_SBCLR = { 7'b0100100, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SBSET = { 7'b0010100, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SBINV = { 7'b0110100, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SBEXT = { 7'b0100100, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };

// ZBP
// grevi
parameter logic [31:0] INSN_GREVI = { 5'b01101, 12'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
// grevi -- pseudo-instructions
parameter logic [31:0] INSN_REV_P =
    { 5'b01101, 2'h?, 5'b00001, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV2_N =
    { 5'b01101, 2'h?, 5'b00010, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV_N =
    { 5'b01101, 2'h?, 5'b00011, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV4_B =
    { 5'b01101, 2'h?, 5'b00100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV2_B =
    { 5'b01101, 2'h?, 5'b00110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV_B =
    { 5'b01101, 2'h?, 5'b00111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV8_H =
    { 5'b01101, 2'h?, 5'b01000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV4_H =
    { 5'b01101, 2'h?, 5'b01100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV2_H =
    { 5'b01101, 2'h?, 5'b01110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV_H =
    { 5'b01101, 2'h?, 5'b01111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV16 =
    { 5'b01101, 2'h?, 5'b01000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV8 =
    { 5'b01101, 2'h?, 5'b11000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV4 =
    { 5'b01101, 2'h?, 5'b11100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV2 =
    { 5'b01101, 2'h?, 5'b11110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_REV =
    { 5'b01101, 2'h?, 5'b11111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
// gorci
parameter logic [31:0] INSN_GORCI = { 5'b00101, 12'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
// gorci -- pseudo-instructions
parameter logic [31:0] INSN_ORC_P =
    { 5'b00101, 2'h?, 5'b00001, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC2_N =
    { 5'b00101, 2'h?, 5'b00010, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC_N =
    { 5'b00101, 2'h?, 5'b00011, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC4_B =
    { 5'b00101, 2'h?, 5'b00100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC2_B =
    { 5'b00101, 2'h?, 5'b00110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC_B =
    { 5'b00101, 2'h?, 5'b00111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC8_H =
    { 5'b00101, 2'h?, 5'b01000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC4_H =
    { 5'b00101, 2'h?, 5'b01100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC2_H =
    { 5'b00101, 2'h?, 5'b01110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC_H =
    { 5'b00101, 2'h?, 5'b01111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC16 =
    { 5'b00101, 2'h?, 5'b01000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC8 =
    { 5'b00101, 2'h?, 5'b11000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC4 =
    { 5'b00101, 2'h?, 5'b11100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC2 =
    { 5'b00101, 2'h?, 5'b11110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORC =
    { 5'b00101, 2'h?, 5'b11111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
// shfli
parameter logic [31:0] INSN_SHFLI = { 6'b000010, 11'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
// shfli -- pseudo-instructions
parameter logic [31:0] INSN_ZIP_N =
    { 5'b00010, 3'h?, 4'b0001, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP2_B =
    { 5'b00010, 3'h?, 4'b0010, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP_B =
    { 5'b00010, 3'h?, 4'b0011, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP4_H =
    { 5'b00010, 3'h?, 4'b0100, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP2_H =
    { 5'b00010, 3'h?, 4'b0110, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP_H =
    { 5'b00010, 3'h?, 4'b0111, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP8 =
    { 5'b00010, 3'h?, 4'b1000, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP4 =
    { 5'b00010, 3'h?, 4'b1100, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP2 =
    { 5'b00010, 3'h?, 4'b1110, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ZIP =
    { 5'b00010, 3'h?, 4'b1111, 5'h?, 3'b001, 5'h?, {OPCODE_OP_IMM} };
// unshfli
parameter logic [31:0] INSN_UNSHFLI = { 6'b000010, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
// unshfli -- pseudo-instructions
parameter logic [31:0] INSN_UNZIP_N =
    { 5'b00010, 3'h?, 4'b0001, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP2_B =
    { 5'b00010, 3'h?, 4'b0010, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP_B =
    { 5'b00010, 3'h?, 4'b0011, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP4_H =
    { 5'b00010, 3'h?, 4'b0100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP2_H =
    { 5'b00010, 3'h?, 4'b0110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP_H =
    { 5'b00010, 3'h?, 4'b0111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP8 =
    { 5'b00010, 3'h?, 4'b1000, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP4 =
    { 5'b00010, 3'h?, 4'b1100, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP2 =
    { 5'b00010, 3'h?, 4'b1110, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_UNZIP =
    { 5'b00010, 3'h?, 4'b1111, 5'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

parameter logic [31:0] INSN_GREV   = { 7'b0110100, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_GORC   = { 7'b0010100, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_SHFL   = { 7'b0000100, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_UNSHFL = { 7'b0000100, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };

// ZBE
parameter logic [31:0] INSN_BDEP = {7'b0100100, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_BEXT = {7'b0000100, 10'h?, 3'b110, 5'h?, {OPCODE_OP} };

// ZBT
parameter logic [31:0] INSN_FSRI = { 5'h?, 1'b1, 11'h?, 3'b101, 5'h?, {OPCODE_OP_IMM} };

parameter logic [31:0] INSN_CMIX = {5'h?, 2'b11, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_CMOV = {5'h?, 2'b11, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_FSL  = {5'h?, 2'b10, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_FSR  = {5'h?, 2'b10, 10'h?, 3'b101, 5'h?, {OPCODE_OP} };

// ZBF
parameter logic [31:0] INSN_BFP  = {7'b0100100, 10'h?, 3'b111, 5'h?, {OPCODE_OP} };

// ZBC
parameter logic [31:0] INSN_CLMUL  = {7'b0000101, 10'h?, 3'b001, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_CLMULR = {7'b0000101, 10'h?, 3'b010, 5'h?, {OPCODE_OP} };
parameter logic [31:0] INSN_CLMULH = {7'b0000101, 10'h?, 3'b011, 5'h?, {OPCODE_OP} };

// ZBR
parameter logic [31:0] INSN_CRC32_B  = {7'b0110000, 5'b10000, 5'h?, 3'b001, 5'h?,  {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_CRC32_H  = {7'b0110000, 5'b10001, 5'h?, 3'b001, 5'h?,  {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_CRC32_W  = {7'b0110000, 5'b10010, 5'h?, 3'b001, 5'h?,  {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_CRC32C_B = {7'b0110000, 5'b11000, 5'h?, 3'b001, 5'h?,  {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_CRC32C_H = {7'b0110000, 5'b11001, 5'h?, 3'b001, 5'h?,  {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_CRC32C_W = {7'b0110000, 5'b11010, 5'h?, 3'b001, 5'h?,  {OPCODE_OP_IMM} };

// LOAD & STORE
parameter logic [31:0] INSN_LOAD    = {25'h?,                            {OPCODE_LOAD } };
parameter logic [31:0] INSN_STORE   = {25'h?,                            {OPCODE_STORE} };

// MISC-MEM
parameter logic [31:0] INSN_FENCE   = { 17'h?,             3'b000, 5'h?, {OPCODE_MISC_MEM} };
parameter logic [31:0] INSN_FENCEI  = { 17'h0,             3'b001, 5'h0, {OPCODE_MISC_MEM} };

// Compressed Instructions
// C0
parameter logic [15:0] INSN_CADDI4SPN  = { 3'b000,       11'h?,                    {OPCODE_C0} };
parameter logic [15:0] INSN_CLW        = { 3'b010,       11'h?,                    {OPCODE_C0} };
parameter logic [15:0] INSN_CSW        = { 3'b110,       11'h?,                    {OPCODE_C0} };

// C1
parameter logic [15:0] INSN_CADDI      = { 3'b000,       11'h?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CJAL       = { 3'b001,       11'h?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CJ         = { 3'b101,       11'h?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CLI        = { 3'b010,       11'h?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CLUI       = { 3'b011,       11'h?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CBEQZ      = { 3'b110,       11'h?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CBNEZ      = { 3'b111,       11'h?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CSRLI      = { 3'b100, 1'h?, 2'b00, 8'h?,              {OPCODE_C1} };
parameter logic [15:0] INSN_CSRAI      = { 3'b100, 1'h?, 2'b01, 8'h?,              {OPCODE_C1} };
parameter logic [15:0] INSN_CANDI      = { 3'b100, 1'h?, 2'b10, 8'h?,              {OPCODE_C1} };
parameter logic [15:0] INSN_CSUB       = { 3'b100, 1'b0, 2'b11, 3'h?, 2'b00, 3'h?, {OPCODE_C1} };
parameter logic [15:0] INSN_CXOR       = { 3'b100, 1'b0, 2'b11, 3'h?, 2'b01, 3'h?, {OPCODE_C1} };
parameter logic [15:0] INSN_COR        = { 3'b100, 1'b0, 2'b11, 3'h?, 2'b10, 3'h?, {OPCODE_C1} };
parameter logic [15:0] INSN_CAND       = { 3'b100, 1'b0, 2'b11, 3'h?, 2'b11, 3'h?, {OPCODE_C1} };

// C2
parameter logic [15:0] INSN_CSLLI      = { 3'b000,       11'h?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_CLWSP      = { 3'b010,       11'h?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_SWSP       = { 3'b110,       11'h?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_CMV        = { 3'b100, 1'b0, 10'h?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_CADD       = { 3'b100, 1'b1, 10'h?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_CEBREAK    = { 3'b100, 1'b1,        5'h0,  5'h0,       {OPCODE_C2} };
parameter logic [15:0] INSN_CJR        = { 3'b100, 1'b0,        5'h0,  5'h0,       {OPCODE_C2} };
parameter logic [15:0] INSN_CJALR      = { 3'b100, 1'b1,        5'h?,  5'h0,       {OPCODE_C2} };

endpackage
