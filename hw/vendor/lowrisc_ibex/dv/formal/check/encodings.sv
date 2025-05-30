// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

`include "../build/ibexspec_instrs.sv"

`ifndef CMP_INSNS
`define CMP_INSNS

`define IS_ITYPE(idx) (`INSTR[6:0] == 7'b0010011 && `INSTR[14:12] == idx)
`define IS_ADDI `IS_ITYPE(3'b000)
`define IS_SLTI `IS_ITYPE(3'b010)
`define IS_SLTIU `IS_ITYPE(3'b011)
`define IS_XORI `IS_ITYPE(3'b100)
`define IS_ORI `IS_ITYPE(3'b110)
`define IS_ANDI `IS_ITYPE(3'b111)
`define IS_ANY_ITYPE ( \
    `IS_ADDI | `IS_SLTI | `IS_SLTIU | `IS_XORI | \
    `IS_ORI | `IS_ANDI \
)

`define ISS_ADDI (`IS_ADDI & `SPEC_ITYPE)
`define ISS_SLTI (`IS_SLTI & `SPEC_ITYPE)
`define ISS_SLTIU (`IS_SLTIU & `SPEC_ITYPE)
`define ISS_XORI (`IS_XORI & `SPEC_ITYPE)
`define ISS_ORI (`IS_ORI & `SPEC_ITYPE)
`define ISS_ANDI (`IS_ANDI & `SPEC_ITYPE)

`define IS_SLLI (`IS_ITYPE(3'b001) && `INSTR[31:25] == 7'b0000000)
`define IS_SRLI (`IS_ITYPE(3'b101) && `INSTR[31:25] == 7'b0000000)
`define IS_SRAI (`IS_ITYPE(3'b101) && `INSTR[31:25] == 7'b0100000)

`define IS_SHIFTIOP (`IS_SLLI | `IS_SRLI | `IS_SRAI)

`define ISS_SLLI (`IS_SLLI & `SPEC_SHIFTIOP)
`define ISS_SRLI (`IS_SRLI & `SPEC_SHIFTIOP)
`define ISS_SRAI (`IS_SRAI & `SPEC_SHIFTIOP)

`define ISS_SHIFTIOP (`ISS_SLLI | `ISS_SRLI | `ISS_SRAI)

`define IS_RTYPE_0(idx) \
    (`INSTR[6:0] == 7'b0110011 && `INSTR[31:25] == 7'b0000000 && `INSTR[14:12] == idx)
`define IS_RTYPE_1(idx) \
    (`INSTR[6:0] == 7'b0110011 && `INSTR[31:25] == 7'b0100000 && `INSTR[14:12] == idx)
`define IS_ADD `IS_RTYPE_0(3'b000)
`define IS_SUB `IS_RTYPE_1(3'b000)
`define IS_SLL `IS_RTYPE_0(3'b001)
`define IS_SLT `IS_RTYPE_0(3'b010)
`define IS_SLTU `IS_RTYPE_0(3'b011)
`define IS_XOR `IS_RTYPE_0(3'b100)
`define IS_SRL `IS_RTYPE_0(3'b101)
`define IS_SRA `IS_RTYPE_1(3'b101)
`define IS_OR `IS_RTYPE_0(3'b110)
`define IS_AND `IS_RTYPE_0(3'b111)

`define ISS_ADD (`IS_ADD & `SPEC_RTYPE)
`define ISS_SUB (`IS_SUB & `SPEC_RTYPE)
`define ISS_SLL (`IS_SLL & `SPEC_RTYPE)
`define ISS_SLT (`IS_SLT & `SPEC_RTYPE)
`define ISS_SLTU (`IS_SLTU & `SPEC_RTYPE)
`define ISS_XOR (`IS_XOR & `SPEC_RTYPE)
`define ISS_SRL (`IS_SRL & `SPEC_RTYPE)
`define ISS_SRA (`IS_SRA & `SPEC_RTYPE)
`define ISS_OR (`IS_OR & `SPEC_RTYPE)
`define ISS_AND (`IS_AND & `SPEC_RTYPE)

`define IS_FENCETYPE(idx) ( \
    `INSTR[31:25] == 4'b0000 && `INSTR[19:15] == 5'b00000 && \
    `INSTR[11:0] == 12'b000000001111 && `INSTR[14:12] == idx)
`define IS_FENCE (`INSTR[31:28] == 4'b0 && `INSTR[19:0] == 20'b0001111)
`define IS_FENCEI (`INSTR == 32'h100f)

`define ISS_FENCE (`IS_FENCE & `SPEC_FENCE)
`define ISS_FENCEI (`IS_FENCEI & `SPEC_FENCEI)

`define IS_LOAD(idx) (`INSTR[6:0] == 7'b0000011 && `INSTR[14:12] == idx)
`define IS_LB `IS_LOAD(3'b000)
`define IS_LH `IS_LOAD(3'b001)
`define IS_LW `IS_LOAD(3'b010)
`define IS_LBU `IS_LOAD(3'b100)
`define IS_LHU `IS_LOAD(3'b101)

`define ISS_LB (`IS_LB & `SPEC_LOAD)
`define ISS_LH (`IS_LH & `SPEC_LOAD)
`define ISS_LW (`IS_LW & `SPEC_LOAD)
`define ISS_LBU (`IS_LBU & `SPEC_LOAD)
`define ISS_LHU (`IS_LHU & `SPEC_LOAD)

`define IS_STORE(idx) (`INSTR[6:0] == 7'b0100011 && `INSTR[14:12] == idx)
`define IS_SB `IS_STORE(3'b000)
`define IS_SH `IS_STORE(3'b001)
`define IS_SW `IS_STORE(3'b010)

`define ISS_SB (`IS_SB & `SPEC_STORE)
`define ISS_SH (`IS_SH & `SPEC_STORE)
`define ISS_SW (`IS_SW & `SPEC_STORE)

`define IS_JAL (`INSTR[6:0] == 7'h6f)
`define IS_JALR (`INSTR[6:0] == 7'h67 && `INSTR[14:12] == 3'b0)

`define ISS_JAL (`IS_JAL & `SPEC_RISCV_JAL)
`define ISS_JALR (`IS_JALR & `SPEC_RISCV_JALR)

`define IS_MTYPE(idx) \
    (`INSTR[6:0] == 7'b0110011 && `INSTR[31:25] == 7'b0000001 && `INSTR[14:12] == idx)
`define IS_MUL `IS_MTYPE(3'b000)
`define IS_MULH `IS_MTYPE(3'b001)
`define IS_MULHSH `IS_MTYPE(3'b010)
`define IS_MULHU `IS_MTYPE(3'b011)
`define IS_DIV `IS_MTYPE(3'b100)
`define IS_DIVU `IS_MTYPE(3'b101)
`define IS_REM `IS_MTYPE(3'b110)
`define IS_REMU `IS_MTYPE(3'b111)

`define ISS_MUL (`IS_MUL & `SPEC_MUL)
`define ISS_MULH (`IS_MULH & `SPEC_MUL)
`define ISS_MULHSH (`IS_MULHSH & `SPEC_MUL)
`define ISS_MULHU (`IS_MULHU & `SPEC_MUL)
`define ISS_DIV (`IS_DIV & `SPEC_DIV)
`define ISS_DIVU (`IS_DIVU & `SPEC_DIV)
`define ISS_REM (`IS_REM & `SPEC_REM)
`define ISS_REMU (`IS_REMU & `SPEC_REM)

`define IS_CSR (`INSTR[6:0] == 7'b1110011 && (|`INSTR[13:12]))
`define CSR_ADDR (`INSTR[31:20])
`define ISS_CSR (`IS_CSR & `SPEC_CSR)

`define IS_ECALL (`INSTR == 32'b00000000000000000000000001110011)
`define ISS_ECALL (`IS_ECALL & `SPEC_ECALL)

`define IS_EBREAK (`INSTR == 32'b00000000000100000000000001110011)
`define ISS_EBREAK (`IS_EBREAK & `SPEC_EBREAK)

`define IS_LUI (`INSTR[6:0] == 7'b0110111)
`define ISS_LUI (`IS_LUI & `SPEC_UTYPE)

`define IS_AUIPC (`INSTR[6:0] == 7'b0010111)
`define ISS_AUIPC (`IS_AUIPC & `SPEC_UTYPE)

`define IS_BTYPE (`INSTR[6:0] == 7'b1100011 && (`INSTR[13] -> `INSTR[14]))
`define ISS_BTYPE (`IS_BTYPE & `SPEC_BTYPE)

`define IS_MRET (`INSTR == 32'b00110000001000000000000001110011)
`define ISS_MRET (`IS_MRET & `SPEC_MRET)

`define IS_WFI (`INSTR == 32'b00010000010100000000000001110011)
`define ISS_WFI (`IS_WFI & `SPEC_WFI)

`endif
