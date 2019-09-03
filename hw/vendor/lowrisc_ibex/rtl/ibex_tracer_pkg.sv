// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_tracer_pkg;
import ibex_pkg::*;

// instruction masks (for tracer)
parameter logic [31:0] INSTR_LUI     = { 25'b?,                           {OPCODE_LUI  } };
parameter logic [31:0] INSTR_AUIPC   = { 25'b?,                           {OPCODE_AUIPC} };
parameter logic [31:0] INSTR_JAL     = { 25'b?,                           {OPCODE_JAL  } };
parameter logic [31:0] INSTR_JALR    = { 17'b?,             3'b000, 5'b?, {OPCODE_JALR } };
// BRANCH
parameter logic [31:0] INSTR_BEQ     = { 17'b?,             3'b000, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSTR_BNE     = { 17'b?,             3'b001, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSTR_BLT     = { 17'b?,             3'b100, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSTR_BGE     = { 17'b?,             3'b101, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSTR_BLTU    = { 17'b?,             3'b110, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSTR_BGEU    = { 17'b?,             3'b111, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSTR_BALL    = { 17'b?,             3'b010, 5'b?, {OPCODE_BRANCH} };
// OPIMM
parameter logic [31:0] INSTR_ADDI    = { 17'b?,             3'b000, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSTR_SLTI    = { 17'b?,             3'b010, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSTR_SLTIU   = { 17'b?,             3'b011, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSTR_XORI    = { 17'b?,             3'b100, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSTR_ORI     = { 17'b?,             3'b110, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSTR_ANDI    = { 17'b?,             3'b111, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSTR_SLLI    = { 7'b0000000, 10'b?, 3'b001, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSTR_SRLI    = { 7'b0000000, 10'b?, 3'b101, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSTR_SRAI    = { 7'b0100000, 10'b?, 3'b101, 5'b?, {OPCODE_OP_IMM} };
// OP
parameter logic [31:0] INSTR_ADD     = { 7'b0000000, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_SUB     = { 7'b0100000, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_SLL     = { 7'b0000000, 10'b?, 3'b001, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_SLT     = { 7'b0000000, 10'b?, 3'b010, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_SLTU    = { 7'b0000000, 10'b?, 3'b011, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_XOR     = { 7'b0000000, 10'b?, 3'b100, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_SRL     = { 7'b0000000, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_SRA     = { 7'b0100000, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_OR      = { 7'b0000000, 10'b?, 3'b110, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_AND     = { 7'b0000000, 10'b?, 3'b111, 5'b?, {OPCODE_OP} };

// SYSTEM
parameter logic [31:0] INSTR_CSRRW   = { 17'b?,             3'b001, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_CSRRS   = { 17'b?,             3'b010, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_CSRRC   = { 17'b?,             3'b011, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_CSRRWI  = { 17'b?,             3'b101, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_CSRRSI  = { 17'b?,             3'b110, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_CSRRCI  = { 17'b?,             3'b111, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_ECALL   = { 12'b000000000000,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_EBREAK  = { 12'b000000000001,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_MRET    = { 12'b001100000010,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_DRET    = { 12'b011110110010,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSTR_WFI     = { 12'b000100000101,         13'b0, {OPCODE_SYSTEM} };

// RV32M
parameter logic [31:0] INSTR_DIV     = { 7'b0000001, 10'b?, 3'b100, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_DIVU    = { 7'b0000001, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_REM     = { 7'b0000001, 10'b?, 3'b110, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_REMU    = { 7'b0000001, 10'b?, 3'b111, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_PMUL    = { 7'b0000001, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_PMUH    = { 7'b0000001, 10'b?, 3'b001, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_PMULHSU = { 7'b0000001, 10'b?, 3'b010, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSTR_PMULHU  = { 7'b0000001, 10'b?, 3'b011, 5'b?, {OPCODE_OP} };

// LOAD & STORE
parameter logic [31:0] INSTR_LOAD    = {25'b?,                            {OPCODE_LOAD } };
parameter logic [31:0] INSTR_STORE   = {25'b?,                            {OPCODE_STORE} };

// MISC-MEM
parameter logic [31:0] INSTR_FENCE   = { 17'b?,             3'b000, 5'b?, {OPCODE_MISC_MEM} };

endpackage
