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
    bit disable_pmp_exception_handler = 0;

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

    if ($value$plusargs("disable_pmp_exception_handler", disable_pmp_exception_handler) &&
        disable_pmp_exception_handler) begin
      cfg.pmp_cfg.enable_pmp_exception_handler = 0;
    end

    super.gen_program();
  endfunction

  // ECALL trap handler
  // For riscv-dv in Ibex, ECALL is no-longer used to end the test.
  // Hence, redefine a simple version here that just increments
  // MEPC+4 then calls 'mret'. (ECALL is always 4-bytes in RV32)
  virtual function void gen_ecall_handler(int hart);
    string instr[$];
    dump_perf_stats(instr);
    gen_register_dump(instr);
    instr = {instr,
             $sformatf("csrr  x%0d, 0x%0x", cfg.gpr[0], MEPC),
             $sformatf("addi  x%0d, x%0d, 4", cfg.gpr[0], cfg.gpr[0]),
             $sformatf("csrw  0x%0x, x%0d", MEPC, cfg.gpr[0])
             };
    instr.push_back("mret");
    gen_section(get_label("ecall_handler", hart), instr);
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

  // Re-define gen_test_done() to override the base-class with an empty implementation.
  // Then, our own overrided gen_program() can append new test_done code.
  virtual function void gen_test_done();
    // empty
  endfunction

  // The test is ended from the UVM testbench, which awaits the following write to
  // the special test-control signature address (signature_addr - 0x4).
  // #FIXME# The existing ECALL trap handler will handle the clean up procedure
  // while awaiting the simulation to be ended.
  virtual function void gen_test_end(input test_result_t result,
                                     ref string instr[$]);
    bit [XLEN-1:0] test_control_addr;
    string str;
    string i = indent; // lint-hack
    test_control_addr = cfg.signature_addr - 4'h4;

    if (cfg.bare_program_mode) begin
      str = {i, "j write_tohost", "\n"};
    end else begin
      // The testbench will await a write of TEST_PASS, and use that to end the test.
      str = {
        {i, $sformatf(  "li x%0d, 0x%0h",       cfg.gpr[1],             test_control_addr), "\n"},
        {i, $sformatf(  "li x%0d, 0x%0h",       cfg.gpr[0],             result), "\n"},
        {i, $sformatf("slli x%0d, x%0d, 8",     cfg.gpr[0], cfg.gpr[0]), "\n"},
        {i, $sformatf("addi x%0d, x%0d, 0x%0h", cfg.gpr[0], cfg.gpr[0], TEST_RESULT), "\n"},
        {i, $sformatf(  "sw x%0d, 0(x%0d)",     cfg.gpr[0], cfg.gpr[1]), "\n"},
      // Still add the ecall insn, to go to the ecall_handler code as before.
        {i, "ecall", "\n"}
      };
    end

    instr.push_back(str);
  endfunction

  virtual function void gen_init_section(int hart);
    // This is a good location to put the test done and fail because PMP tests expect these
    // sequences to be before the main function.
    string instr[$];

    super.gen_init_section(hart);

    gen_test_end(.result(TEST_PASS), .instr(instr));
    instr_stream = {instr_stream,
                    {format_string("test_done:", LABEL_STR_LEN)},
                    instr};
    instr.delete();
    gen_test_end(.result(TEST_FAIL), .instr(instr));
    instr_stream = {instr_stream,
                    {format_string("test_fail:", LABEL_STR_LEN)},
                    instr};
  endfunction

endclass
