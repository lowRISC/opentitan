// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//-----------------------------------------------------------------------------------------
// RISC-V assembly program generator for ibex
//-----------------------------------------------------------------------------------------

class ibex_asm_program_gen extends riscv_asm_program_gen;

  `uvm_object_utils(ibex_asm_program_gen)
  `uvm_object_new

  virtual function void gen_program_header();
    // Override the cfg value, below fields are not supported by ibex
    cfg.mstatus_mprv = 0;
    cfg.mstatus_mxr  = 0;
    cfg.mstatus_sum  = 0;
    cfg.mstatus_tvm  = 0;
    // Disable below fields checking against spike as spike implementation is different compared
    // with ibex.
    cfg.check_misa_init_val = 1'b0;
    cfg.check_xstatus = 1'b0;
    // The ibex core load the program from 0x80
    // Some address is reserved for hardware interrupt handling, need to decide if we need to copy
    // the init program from crt0.S later.
    instr_stream.push_back(".macro init");
    instr_stream.push_back(".endm");
    instr_stream.push_back(".section .text.init");
    instr_stream.push_back(".globl _start");
    instr_stream.push_back(".option norvc");
    // 0x0 - 0x4F is reserved for trap/interrupt handling
    repeat (20) begin
      instr_stream.push_back("j mtvec_handler");
    end
    // 0x50 debug mode entry
    instr_stream.push_back("j debug_rom");
    // 0x54 debug mode exception handler
    instr_stream.push_back("j debug_exception");
    // Align the start section to 0x80
    instr_stream.push_back(".align 7");
    instr_stream.push_back("_start: j _reset_entry");
    // ibex reserves 0x84-0x8C for trap handling, redirect everything mtvec_handler
    // 0x84 illegal instruction
    instr_stream.push_back("j mtvec_handler");
    // 0x88 ECALL instruction handler
    instr_stream.push_back("j mtvec_handler");
    // 0x8C LSU error
    instr_stream.push_back("j mtvec_handler");
    instr_stream.push_back(".option rvc");
    // Starting point of the reset entry
    instr_stream.push_back("_reset_entry:");
  endfunction

endclass
