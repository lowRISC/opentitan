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
parameter logic [31:0] INSN_LUI     = { 25'b?,                           {OPCODE_LUI  } };
parameter logic [31:0] INSN_AUIPC   = { 25'b?,                           {OPCODE_AUIPC} };
parameter logic [31:0] INSN_JAL     = { 25'b?,                           {OPCODE_JAL  } };
parameter logic [31:0] INSN_JALR    = { 17'b?,             3'b000, 5'b?, {OPCODE_JALR } };

// BRANCH
parameter logic [31:0] INSN_BEQ     = { 17'b?,             3'b000, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BNE     = { 17'b?,             3'b001, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BLT     = { 17'b?,             3'b100, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BGE     = { 17'b?,             3'b101, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BLTU    = { 17'b?,             3'b110, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BGEU    = { 17'b?,             3'b111, 5'b?, {OPCODE_BRANCH} };
parameter logic [31:0] INSN_BALL    = { 17'b?,             3'b010, 5'b?, {OPCODE_BRANCH} };

// OPIMM
parameter logic [31:0] INSN_ADDI    = { 17'b?,             3'b000, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SLTI    = { 17'b?,             3'b010, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SLTIU   = { 17'b?,             3'b011, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_XORI    = { 17'b?,             3'b100, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ORI     = { 17'b?,             3'b110, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_ANDI    = { 17'b?,             3'b111, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SLLI    = { 7'b0000000, 10'b?, 3'b001, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SRLI    = { 7'b0000000, 10'b?, 3'b101, 5'b?, {OPCODE_OP_IMM} };
parameter logic [31:0] INSN_SRAI    = { 7'b0100000, 10'b?, 3'b101, 5'b?, {OPCODE_OP_IMM} };

// OP
parameter logic [31:0] INSN_ADD     = { 7'b0000000, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_SUB     = { 7'b0100000, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_SLL     = { 7'b0000000, 10'b?, 3'b001, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_SLT     = { 7'b0000000, 10'b?, 3'b010, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_SLTU    = { 7'b0000000, 10'b?, 3'b011, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_XOR     = { 7'b0000000, 10'b?, 3'b100, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_SRL     = { 7'b0000000, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_SRA     = { 7'b0100000, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_OR      = { 7'b0000000, 10'b?, 3'b110, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_AND     = { 7'b0000000, 10'b?, 3'b111, 5'b?, {OPCODE_OP} };

// SYSTEM
parameter logic [31:0] INSN_CSRRW   = { 17'b?,             3'b001, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRS   = { 17'b?,             3'b010, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRC   = { 17'b?,             3'b011, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRWI  = { 17'b?,             3'b101, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRSI  = { 17'b?,             3'b110, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_CSRRCI  = { 17'b?,             3'b111, 5'b?, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_ECALL   = { 12'b000000000000,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_EBREAK  = { 12'b000000000001,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_MRET    = { 12'b001100000010,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_DRET    = { 12'b011110110010,         13'b0, {OPCODE_SYSTEM} };
parameter logic [31:0] INSN_WFI     = { 12'b000100000101,         13'b0, {OPCODE_SYSTEM} };

// RV32M
parameter logic [31:0] INSN_DIV     = { 7'b0000001, 10'b?, 3'b100, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_DIVU    = { 7'b0000001, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_REM     = { 7'b0000001, 10'b?, 3'b110, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_REMU    = { 7'b0000001, 10'b?, 3'b111, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_PMUL    = { 7'b0000001, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_PMUH    = { 7'b0000001, 10'b?, 3'b001, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_PMULHSU = { 7'b0000001, 10'b?, 3'b010, 5'b?, {OPCODE_OP} };
parameter logic [31:0] INSN_PMULHU  = { 7'b0000001, 10'b?, 3'b011, 5'b?, {OPCODE_OP} };

// LOAD & STORE
parameter logic [31:0] INSN_LOAD    = {25'b?,                            {OPCODE_LOAD } };
parameter logic [31:0] INSN_STORE   = {25'b?,                            {OPCODE_STORE} };

// MISC-MEM
parameter logic [31:0] INSN_FENCE   = { 17'b?,             3'b000, 5'b?, {OPCODE_MISC_MEM} };
parameter logic [31:0] INSN_FENCEI  = { 17'b0,             3'b001, 5'b0, {OPCODE_MISC_MEM} };

// Compressed Instructions
// C0
parameter logic [15:0] INSN_CADDI4SPN  = { 3'b000,       11'b?,                    {OPCODE_C0} };
parameter logic [15:0] INSN_CLW        = { 3'b010,       11'b?,                    {OPCODE_C0} };
parameter logic [15:0] INSN_CSW        = { 3'b110,       11'b?,                    {OPCODE_C0} };

// C1
parameter logic [15:0] INSN_CADDI      = { 3'b000,       11'b?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CJAL       = { 3'b001,       11'b?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CJ         = { 3'b101,       11'b?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CLI        = { 3'b010,       11'b?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CLUI       = { 3'b011,       11'b?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CBEQZ      = { 3'b110,       11'b?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CBNEZ      = { 3'b111,       11'b?,                    {OPCODE_C1} };
parameter logic [15:0] INSN_CSRLI      = { 3'b100, 1'b?, 2'b00, 8'b?,              {OPCODE_C1} };
parameter logic [15:0] INSN_CSRAI      = { 3'b100, 1'b?, 2'b01, 8'b?,              {OPCODE_C1} };
parameter logic [15:0] INSN_CANDI      = { 3'b100, 1'b?, 2'b10, 8'b?,              {OPCODE_C1} };
parameter logic [15:0] INSN_CSUB       = { 3'b100, 1'b0, 2'b11, 3'b?, 2'b00, 3'b?, {OPCODE_C1} };
parameter logic [15:0] INSN_CXOR       = { 3'b100, 1'b0, 2'b11, 3'b?, 2'b01, 3'b?, {OPCODE_C1} };
parameter logic [15:0] INSN_COR        = { 3'b100, 1'b0, 2'b11, 3'b?, 2'b10, 3'b?, {OPCODE_C1} };
parameter logic [15:0] INSN_CAND       = { 3'b100, 1'b0, 2'b11, 3'b?, 2'b11, 3'b?, {OPCODE_C1} };

// C2
parameter logic [15:0] INSN_CSLLI      = { 3'b000,       11'b?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_CLWSP      = { 3'b010,       11'b?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_SWSP       = { 3'b110,       11'b?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_CMV        = { 3'b100, 1'b0, 10'b?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_CADD       = { 3'b100, 1'b1, 10'b?,                    {OPCODE_C2} };
parameter logic [15:0] INSN_CEBREAK    = { 3'b100, 1'b1,        5'b0,  5'b0,       {OPCODE_C2} };
parameter logic [15:0] INSN_CJR        = { 3'b100, 1'b0,        5'b?,  5'b0,       {OPCODE_C2} };
parameter logic [15:0] INSN_CJALR      = { 3'b100, 1'b1,        5'b?,  5'b0,       {OPCODE_C2} };

endpackage
