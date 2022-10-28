// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//-----------------------------------------------------------------------------------------
// RISC-V assembly program generator for ibex
//-----------------------------------------------------------------------------------------

class ibex_asm_program_gen extends riscv_asm_program_gen;

  `uvm_object_utils(ibex_asm_program_gen)
  `uvm_object_new

  virtual function void gen_program();
    default_include_csr_write = {
      MSCRATCH,
      MVENDORID,
      MARCHID,
      MHARTID,
      MCONFIGPTR,
      MENVCFG,
      MSTATUSH,
      MIMPID,
      MCYCLE,
      MCYCLEH,
      MHPMEVENT3,
      MHPMEVENT4,
      MHPMEVENT5,
      MHPMEVENT6,
      MHPMEVENT7,
      MHPMEVENT8,
      MHPMEVENT9,
      MHPMEVENT10,
      MHPMCOUNTER3,
      MHPMCOUNTER4,
      MHPMCOUNTER5,
      MHPMCOUNTER6,
      MHPMCOUNTER7,
      MHPMCOUNTER8,
      MHPMCOUNTER9,
      MHPMCOUNTER10,
      MHPMCOUNTER3H,
      MHPMCOUNTER4H,
      MHPMCOUNTER5H,
      MHPMCOUNTER6H,
      MHPMCOUNTER7H,
      MHPMCOUNTER8H,
      MHPMCOUNTER9H,
      MHPMCOUNTER10H,
      12'h7c1 // SECURESEED
    };

    riscv_csr_instr::create_csr_filter(cfg);

    super.gen_program();
  endfunction

  virtual function void gen_program_header();
    // Override the mstatus_mprv config because there is no current way to randomize writing to
    // mstatus.mprv in riscv-dv (it's constrained by set_mstatus_mprv argument to have either
    // 1 or 0 for the duration of the run)
    if (cfg.set_mstatus_mprv)
      cfg.mstatus_mprv = $urandom_range(1);
    // Override the cfg value, below fields are not supported by ibex
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

  // Generate "test_done" section.
  // The test is ended from the UVM testbench, which awaits the following write to
  // the special test-control signature address (signature_addr - 0x4).
  // The ECALL trap handler will handle the clean up procedure while awaiting the
  // simulation to be ended.
  virtual function void gen_test_done();
    bit [XLEN-1:0] test_control_addr;
    string str;
    string i = indent; // lint-hack
    test_control_addr = cfg.signature_addr - 4'h4;

    str = {str,
      {format_string("test_done:", LABEL_STR_LEN), "\n"},
      {i, "li gp, 1", "\n"}
    };

    if (cfg.bare_program_mode) begin
      str = {str,
        {i, "j write_tohost", "\n"}
      };
    end else begin
      // The testbench will await a write of TEST_PASS, and use that to end the test.
      str = {str,
        {i, $sformatf(  "li x%0d, 0x%0h",       cfg.gpr[1],             test_control_addr), "\n"},
        {i, $sformatf(  "li x%0d, 0x%0h",       cfg.gpr[0],             TEST_PASS), "\n"},
        {i, $sformatf("slli x%0d, x%0d, 8",     cfg.gpr[0], cfg.gpr[0]), "\n"},
        {i, $sformatf("addi x%0d, x%0d, 0x%0h", cfg.gpr[0], cfg.gpr[0], TEST_RESULT), "\n"},
        {i, $sformatf(  "sw x%0d, 0(x%0d)",     cfg.gpr[0], cfg.gpr[1]), "\n"},
      // Still add the ecall insn, to go to the ecall_handler code as before.
        {i, "ecall", "\n"}
      };
    end

    instr_stream.push_back(str);
  endfunction

endclass
