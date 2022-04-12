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
    instr_stream.push_back(".section .text");
    instr_stream.push_back(".globl _start");
    instr_stream.push_back(".option norvc");
    // 0x0 debug mode entry
    instr_stream.push_back("j debug_rom");
    // 0x4 debug mode exception handler
    instr_stream.push_back("j debug_exception");
    // Align the start section to 0x80
    instr_stream.push_back(".align 7");
    instr_stream.push_back(".option rvc");
    instr_stream.push_back("_start:");
  endfunction

  virtual function void init_custom_csr(ref string instr[$]);
    // Write 1 to cpuctrl.icache_enable to enable Icache during simulation
    instr.push_back("csrwi 0x7c0, 1");
  endfunction

endclass
