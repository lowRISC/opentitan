/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
 * Copyright 2022 Coverify Systems Technology
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------------------
// RISC-V assembly program generator
//
// This is the main class to generate a complete RISC-V program, including the init routine,
// instruction section, data section, stack section, page table, interrupt and exception
// handling etc. Check gen_program() function to see how the program is generated.
//-----------------------------------------------------------------------------------------
module riscv.gen.riscv_asm_program_gen;

import riscv.gen.riscv_signature_pkg: core_status_t, signature_type_t, test_result_t;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;

import riscv.gen.riscv_instr_pkg: privileged_reg_t, privileged_mode_t,
  exception_cause_t, interrupt_cause_t, get_label, indent, hart_prefix,
  riscv_instr_group_t, satp_mode_t, program_id_t, format_string, misa_ext_t,
  vreg_init_method_t, mem_region_t, mtvec_mode_t, push_gpr_to_kernel_stack,
  pop_gpr_from_kernel_stack, riscv_reg_t,
  DATA_WIDTH, SINGLE_PRECISION_FRACTION_BITS, LABEL_STR_LEN,
  DOUBLE_PRECISION_FRACTION_BITS;
import riscv.gen.target: support_pmp, max_interrupt_vector_num,
  implemented_csr, support_debug_mode, supported_isa,
  supported_privileged_mode, support_umode_trap,
  NUM_GPR, ELEN, VLEN, NUM_VEC_GPR, NUM_FLOAT_GPR, NUM_HARTS, SATP_MODE, XLEN;
import riscv.gen.isa.riscv_instr: riscv_instr;
import riscv.gen.riscv_instr_stream: riscv_instr_stream, riscv_rand_instr_stream;
import riscv.gen.riscv_data_page_gen: riscv_data_page_gen;
import riscv.gen.riscv_instr_sequence: riscv_instr_sequence;
import riscv.gen.riscv_callstack_gen: riscv_callstack_gen;
import riscv.gen.riscv_page_table_list: riscv_page_table_list;
import riscv.gen.riscv_privileged_common_seq: riscv_privileged_common_seq;


import std.algorithm: canFind;
import std.string: toLower;
import std.format: format;

import esdl.data.queue: Queue;
import esdl.data.bvec: ubvec, toubvec;
import esdl.rand: randomize;
import esdl.base.rand: urandom, shuffle;
import esdl.solver: CstVecDistSolver, CstVecDistRange;
import esdl.base.cmdl: CommandLine;

import uvm;

class riscv_asm_program_gen : uvm_object
{
  riscv_instr_gen_config              cfg;
  riscv_data_page_gen                 data_page_gen;
  // User mode programs
  riscv_instr_sequence[NUM_HARTS]     main_program;
  riscv_instr_sequence[][NUM_HARTS]   sub_program;
  riscv_asm_program_gen               debug_rom;
  // Kernel programs
  // These programs are called in the interrupt/exception handling routine based on the privileged
  // mode settings. For example, when the interrupt/exception is delegated to S-mode, if both SUM
  // and MPRV equal 1, kernel program can fetch/load/store from U-mode pages,
  // umode_program is designed for this purpose. There can be other cases that
  // instruction can only be fetched from S-mode pages but load/store can access U-mode pages, or
  // everything needs to be in S-mode pages.
  riscv_instr_sequence                umode_program;
  riscv_instr_sequence                smode_program;
  riscv_instr_sequence                smode_lsu_program;
  riscv_instr_stream[]                directed_instr;
  string[]                            instr_stream;
  riscv_callstack_gen                 callstack_gen;
  riscv_privileged_common_seq         privil_seq;
  // Directed instruction ratio, occurance per 1000 instructions
  uint[string]                        directed_instr_stream_ratio;
  riscv_page_table_list!(SATP_MODE)   page_table_list;
  int                                 hart;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  //---------------------------------------------------------------------------------------
  // Main function to generate the whole program
  //---------------------------------------------------------------------------------------

  // This is the main function to generate all sections of the program.
  void gen_program() {
    instr_stream.length = 0;
    // Generate program header
    gen_program_header();
    for (int hart = 0; hart < cfg.num_of_harts; hart++) {
      string[] sub_program_name;
      instr_stream ~= (format("h%0d_start:", hart));
      if (!cfg.bare_program_mode) {
        setup_misa();
        // Create all page tables
        create_page_table(hart);
        // Setup privileged mode registers and enter target privileged mode
        pre_enter_privileged_mode(hart);
      }
      // Init section
      gen_init_section(hart);
      // If PMP is supported, we want to generate the associated trap handlers and the test_done
      // section at the start of the program so we can allow access through the pmpcfg0 CSR
      if (support_pmp && !cfg.bare_program_mode) {
        gen_trap_handlers(hart);
        // Ecall handler
        gen_ecall_handler(hart);
        // Instruction fault handler
        gen_instr_fault_handler(hart);
        // Load fault handler
        gen_load_fault_handler(hart);
        // Store fault handler
        gen_store_fault_handler(hart);
	if (hart == 0) {
	  gen_test_done();
	}
      }
      // Generate sub program
      gen_sub_program(hart, sub_program[hart], sub_program_name, cfg.num_of_sub_program);
      // Generate main program
      main_program[hart] = riscv_instr_sequence.type_id.create(get_label("main", hart));
      main_program[hart].instr_cnt = cfg.main_program_instr_cnt;
      main_program[hart].is_debug_program = 0;
      main_program[hart].label_name = main_program[hart].get_name();
      generate_directed_instr_stream(hart,
                                     main_program[hart].label_name,
                                     main_program[hart].instr_cnt,
                                     1,
				     false,
                                     main_program[hart].directed_instr
				     );
      main_program[hart].cfg = cfg;
      main_program[hart].randomize();
      main_program[hart].gen_instr(true, cfg.no_branch_jump);
      // Setup jump instruction among main program and sub programs
      gen_callstack(main_program[hart], sub_program[hart], sub_program_name,
                    cfg.num_of_sub_program);
      uvm_info(get_full_name(), "Generating callstack...done", UVM_LOW);
      main_program[hart].post_process_instr();
      uvm_info(get_full_name(), "Post-processing main program...done", UVM_LOW);
      main_program[hart].generate_instr_stream();
      uvm_info(get_full_name(), "Generating main program instruction stream...done", UVM_LOW);
      instr_stream ~= main_program[hart].instr_string_list.toArray();
      // If PMP is supported, need to jump from end of main program to test_done section at the end
      // of main_program, as the test_done will have moved to the beginning of the program
      instr_stream ~= format("%sla x%0d, test_done", indent, cfg.scratch_reg);
      instr_stream ~= format("%sjalr x0, x%0d, 0", indent, cfg.scratch_reg);
      // Test done section
      // If PMP isn't supported, generate this in the normal location
      if ((hart == 0) & !support_pmp) {
        gen_test_done();
      }
      // Shuffle the sub programs and insert to the instruction stream
      insert_sub_program(sub_program[hart], instr_stream);
      uvm_info(get_full_name(), "Inserting sub-programs...done", UVM_LOW);
      uvm_info(get_full_name(), "Main/sub program generation...done", UVM_LOW);
      // Program end
      gen_program_end(hart);
      if (!cfg.bare_program_mode) {
        // Generate debug rom section
        if (support_debug_mode) {
          gen_debug_rom(hart);
        }
      }
      gen_section((hart_prefix(hart) ~ "instr_end"), ["nop"]);
    }
    for (int hart = 0; hart < cfg.num_of_harts; hart++) {
      // Starting point of data section
      gen_data_page_begin(hart);
      if (!cfg.no_data_page) {
        // User data section
        gen_data_page(hart);
        // AMO memory region
        if ((hart == 0) && (canFind(supported_isa, riscv_instr_group_t.RV32A))) {
          gen_data_page(hart, false, true);
	}
      }
      // Stack section
      gen_stack_section(hart);
      if (!cfg.bare_program_mode) {
        // Generate kernel program/data/stack section
        gen_kernel_sections(hart);
      }
      // Page table
      if (!cfg.bare_program_mode) {
        gen_page_table_section(hart);
      }
    }
  }

  //---------------------------------------------------------------------------------------
  // Generate kernel program/data/stack sections
  //---------------------------------------------------------------------------------------
  void gen_kernel_sections(int hart) {
    if (SATP_MODE != satp_mode_t.BARE) {
      instr_stream ~= ".align 12";
    }
    else {
      instr_stream ~= ".align 2";
    }
    instr_stream ~= get_label("kernel_instr_start:", hart);
    instr_stream ~= ".text";
    // Kernel programs
    if (cfg.virtual_addr_translation_on) {
      umode_program = riscv_instr_sequence.type_id.create(get_label("umode_program", hart));
      gen_kernel_program(hart, umode_program);
      smode_program = riscv_instr_sequence.type_id.create(get_label("smode_program", hart));
      gen_kernel_program(hart, smode_program);
      smode_lsu_program = riscv_instr_sequence.type_id.
	create(get_label("smode_lsu_program", hart));
      gen_kernel_program(hart, smode_lsu_program);
    }
    // All trap/interrupt handling is in the kernel region
    // Trap/interrupt delegation to user mode is not supported now
    // Trap handler
    gen_all_trap_handler(hart);
    // Interrupt handling subroutine
    foreach (mode; supported_privileged_mode) {
      gen_interrupt_handler_section(mode, hart);
    }
    instr_stream ~= get_label("kernel_instr_end: nop", hart);
    // User stack and data pages may not be accessible when executing trap handling programs in
    // machine/supervisor mode. Generate separate kernel data/stack sections to solve it.
    if (cfg.virtual_addr_translation_on) {
      if (SATP_MODE != satp_mode_t.BARE) {
        instr_stream ~= ".align 12";
      } else {
        instr_stream ~= ".align 2";
      }
      // Kernel data pages
      instr_stream ~= get_label("kernel_data_start:", hart);
      if(!cfg.no_data_page) {
        // Data section
        gen_data_page(hart, true);
      }
    }
    // Kernel stack section
    gen_kernel_stack_section(hart);
  }

  void gen_kernel_program(int hart, riscv_instr_sequence seq) {
    seq.instr_cnt = cfg.kernel_program_instr_cnt;
    generate_directed_instr_stream(hart,
                                   seq.get_name(),
                                   seq.instr_cnt,
                                   0,
				   true,
                                   seq.directed_instr,
				   );
    seq.label_name = seq.get_name();
    seq.is_debug_program = 0;
    seq.cfg = cfg;
    seq.randomize();
    seq.gen_instr(false, cfg.no_branch_jump);
    seq.post_process_instr();
    seq.generate_instr_stream();
    instr_stream ~= seq.instr_string_list.toArray();
  }

  //---------------------------------------------------------------------------------------
  // Generate any subprograms and set up the callstack
  //---------------------------------------------------------------------------------------

  void gen_sub_program(int hart,
		       ref riscv_instr_sequence[] sub_program,
		       ref string[] sub_program_name,
		       in int num_sub_program,
		       bool is_debug = false,
		       string prefix = "sub") {
    if (num_sub_program > 0) {
      sub_program.length = num_sub_program;
      foreach (j, ref subp; sub_program) {
        subp = riscv_instr_sequence.type_id.create(get_label(format("%s_%0d", prefix, j + 1), hart));
        uvm_info(get_full_name(), format("sub program name: %s", subp.get_name()), UVM_LOW);
        subp.is_debug_program = is_debug;
        if (is_debug) {
          subp.instr_cnt = cfg.debug_sub_program_instr_cnt[j];
        } else {
          subp.instr_cnt = cfg.sub_program_instr_cnt[j];
        }
        generate_directed_instr_stream(hart,
                                       subp.get_name(),
                                       subp.instr_cnt,
				       0,
				       false,
				       subp.directed_instr);
        subp.label_name = subp.get_name();
        subp.cfg = cfg;
        subp.randomize();
        subp.gen_instr(false, cfg.no_branch_jump);
        sub_program_name ~= subp.label_name;
      }
    }
  }

  void gen_callstack(riscv_instr_sequence main_program,
		     ref riscv_instr_sequence [] sub_program,
		     ref string[] sub_program_name,
		     in int num_sub_program) {
    if(num_sub_program != 0) {
      callstack_gen = riscv_callstack_gen.type_id.create("callstack_gen");
      callstack_gen.init(num_sub_program+1);
      uvm_info(get_full_name(), "Randomizing call stack", UVM_LOW);
      callstack_gen.randomize();
      program_id_t pid;
      int idx;
      // Insert the jump instruction based on the call stack
      foreach (i, ref prog; callstack_gen.program_h) {
	foreach (j, ref subp; prog.sub_program_id) {
	  idx++;
	  pid = cast(ubvec!16) (prog.sub_program_id[j] - 1);
	  uvm_info(get_full_name(),
		   format("Gen jump instr %0d -> sub[%0d] %0d", i, j, pid+1), UVM_LOW);
	  if (i == 0)
	    main_program.insert_jump_instr(sub_program_name[pid], idx);
	  else
	    sub_program[i-1].insert_jump_instr(sub_program_name[pid], idx);
	}
      }
      // else {
      // 	uvm_fatal(get_full_name(), "Failed to generate callstack");
      // }
    }
    uvm_info(get_full_name(), "Randomizing call stack..done", UVM_LOW);
  }

  void insert_sub_program(riscv_instr_sequence[] sub_program,
			  ref Queue!string instr_string_list) {
    sub_program.shuffle();
    foreach(subp; sub_program) {
      subp.post_process_instr();
      subp.generate_instr_stream();
      instr_string_list ~= subp.instr_string_list;
    }
  }

  void insert_sub_program(riscv_instr_sequence[] sub_program,
			  ref string[] instr_string_list) {
    sub_program.shuffle();
    foreach(subp; sub_program) {
      subp.post_process_instr();
      subp.generate_instr_stream();
      instr_string_list ~= subp.instr_string_list.toArray;
    }
  }

  //---------------------------------------------------------------------------------------
  // Major sections - init, stack, data, test_done etc.
  //---------------------------------------------------------------------------------------

  void gen_program_header() {
    string[] str;
    instr_stream ~= ".include \"user_define.h\"";
    instr_stream ~= ".globl _start";
    instr_stream ~= ".section .text";
    if (cfg.disable_compressed_instr) {
      instr_stream ~= ".option norvc;";
    }
    str ~= ".include \"user_init.s\"";
    str ~= format("csrr x5, 0x%0x", privileged_reg_t.MHARTID);
    for (int hart = 0; hart < cfg.num_of_harts; hart++) {
      str ~= format("li x6, %0d", hart);
      str ~= format("beq x5, x6, %0df", hart);
    }
    gen_section("_start", str);
    for (int hart = 0; hart < cfg.num_of_harts; hart++) {
      instr_stream ~= format("%0d: la x%0d, h%0d_start", hart, cfg.scratch_reg, hart);
      instr_stream ~= format("jalr x0, x%0d, 0", cfg.scratch_reg);
    }
  }

  void gen_program_end(int hart) {
    if (hart == 0) {
      // Use write_tohost to terminate spike simulation
      gen_section("write_tohost", ["sw gp, tohost, t5"]);
      gen_section("_exit", ["j write_tohost"]);
    }
  }

  void gen_data_page_begin(int hart) {
    instr_stream ~= ".section .data";
    if (hart == 0) {
      instr_stream ~= ".align 6; .global tohost; tohost: .dword 0;";
      instr_stream ~= ".align 6; .global fromhost; fromhost: .dword 0;";
    }
  }

  void gen_data_page(int hart, bool is_kernel = false, bool amo = false) {
    string data_page;
    data_page_gen = riscv_data_page_gen.type_id.create("data_page_gen");
    data_page_gen.cfg = cfg;
    data_page_gen.gen_data_page(hart, cfg.data_page_pattern, is_kernel, amo);
    instr_stream ~= data_page_gen.data_page_str;
  }

  // Generate the user stack section
  void gen_stack_section(int hart) {
    string hart_prefix_string = hart_prefix(hart);
    if (cfg.use_push_data_section) {
      instr_stream ~= format(".pushsection .%0suser_stack,\"aw\",@progbits;",
			     hart_prefix_string);
    } else {
      instr_stream ~= format(".section .%0suser_stack,\"aw\",@progbits;",
			     hart_prefix_string);
    }
    if (SATP_MODE != satp_mode_t.BARE) {
      instr_stream ~= ".align 12";
    } else {
      instr_stream ~= ".align 2";
    }
    instr_stream ~= get_label("user_stack_start:", hart);
    instr_stream ~= format(".rept %0d", cfg.stack_len - 1);
    instr_stream ~= format(".%0dbyte 0x0", XLEN/8);
    instr_stream ~= ".endr";
    instr_stream ~= get_label("user_stack_end:", hart);
    instr_stream ~= format(".%0dbyte 0x0", XLEN/8);
    if (cfg.use_push_data_section) {
      instr_stream ~= ".popsection;";
    }
  }

  // The kernal stack is used to save user program context before executing exception handling
  void gen_kernel_stack_section(int hart) {
    string hart_prefix_string = hart_prefix(hart);
    if (cfg.use_push_data_section) {
      instr_stream ~= format(".pushsection .%0skernel_stack,\"aw\",@progbits;",
			     hart_prefix_string);
    } else {
      instr_stream ~= format(".section .%0skernel_stack,\"aw\",@progbits;",
			     hart_prefix_string);
    }
    if (SATP_MODE != satp_mode_t.BARE) {
      instr_stream ~= ".align 12";
    } else {
      instr_stream ~= ".align 2";
    }
    instr_stream ~= get_label("kernel_stack_start:", hart);
    instr_stream ~= format(".rept %0d", cfg.kernel_stack_len - 1);
    instr_stream ~= format(".%0dbyte 0x0", XLEN/8);
    instr_stream ~= ".endr";
    instr_stream ~= get_label("kernel_stack_end:", hart);
    instr_stream ~= format(".%0dbyte 0x0", XLEN/8);
    if (cfg.use_push_data_section) {
      instr_stream ~= ".popsection;";
    }
  }

  void gen_init_section(int hart) {
    string str;
    str = format_string(get_label("init:", hart), LABEL_STR_LEN);
    instr_stream ~= str;
    if (cfg.enable_floating_point) {
      init_floating_point_gpr();
    }
    init_gpr();
    // Init stack pointer to point to the end of the user stack
    str = indent ~ format("la x%0d, %0suser_stack_end", cfg.sp, hart_prefix(hart));
    instr_stream ~= str;
    if (cfg.enable_vector_extension) {
      randomize_vec_gpr_and_csr();
    }
    core_is_initialized();
    gen_dummy_csr_write(); // TODO add a way to disable xStatus read
    if (support_pmp) {
      str = indent ~  "j main";
      instr_stream ~= str;
    }
  }

  // Setup MISA based on supported extensions
  void setup_misa() {
    ubvec!XLEN   misa;
    misa[XLEN-2..XLEN] = (XLEN == 32) ? toubvec!2(0b01) :
      (XLEN == 64) ? toubvec!2(0b10) : toubvec!2(0b11);
    if (cfg.check_misa_init_val) {
      instr_stream ~= indent ~ format("csrr x15, 0x%0x", privileged_reg_t.MISA);
    }
    foreach (sisa; supported_isa) {
      switch  (sisa) {
      case riscv_instr_group_t.RV32C, riscv_instr_group_t.RV64C,
	riscv_instr_group_t.RV128C: misa[misa_ext_t.MISA_EXT_C] = true; break;
      case riscv_instr_group_t.RV32I, riscv_instr_group_t.RV64I,
	riscv_instr_group_t.RV128I: misa[misa_ext_t.MISA_EXT_I] = true; break;
      case riscv_instr_group_t.RV32M,
	riscv_instr_group_t.RV64M: misa[misa_ext_t.MISA_EXT_M] = true; break;
      case riscv_instr_group_t.RV32A,
	riscv_instr_group_t.RV64A: misa[misa_ext_t.MISA_EXT_A] = true; break;
      case riscv_instr_group_t.RV32B,
	riscv_instr_group_t.RV64B: misa[misa_ext_t.MISA_EXT_B] = true; break;
      case riscv_instr_group_t.RV32F, riscv_instr_group_t.RV64F,
	riscv_instr_group_t.RV32FC: misa[misa_ext_t.MISA_EXT_F] = true; break;
      case riscv_instr_group_t.RV32D, riscv_instr_group_t.RV64D,
	riscv_instr_group_t.RV32DC: misa[misa_ext_t.MISA_EXT_D] = true; break;
      case riscv_instr_group_t.RVV: misa[misa_ext_t.MISA_EXT_V] = true; break;
      case riscv_instr_group_t.RV32X,
	riscv_instr_group_t.RV64X: misa[misa_ext_t.MISA_EXT_X] = true; break;
      case riscv_instr_group_t.RV32ZBA,	riscv_instr_group_t.RV32ZBB,
	riscv_instr_group_t.RV32ZBC, riscv_instr_group_t.RV32ZBS,
        riscv_instr_group_t.RV64ZBA, riscv_instr_group_t.RV64ZBB,
	riscv_instr_group_t.RV64ZBC, riscv_instr_group_t.RV64ZBS: break; // No Misa bit for Zb* extensions
      default : uvm_fatal(get_full_name(), format("%0s is not yet supported", sisa));
      }
    }
    if (canFind(supported_privileged_mode, privileged_mode_t.SUPERVISOR_MODE)) {
      misa[misa_ext_t.MISA_EXT_S] = true;
    }
    instr_stream ~= indent ~ format("li x%0d, 0x%0x", cfg.gpr[0], misa);
    instr_stream ~= indent ~ format("csrw 0x%0x, x%0d", privileged_reg_t.MISA, cfg.gpr[0]);
  }

  // Write to the signature_addr with values to indicate to the core testbench
  // that is safe to start sending interrupt and debug stimulus
  void core_is_initialized() {
    string[] instr;
    if (cfg.require_signature_addr) {
      if (cfg.signature_addr != 0xdead_beef) {
        gen_signature_handshake(instr, signature_type_t.CORE_STATUS, core_status_t.INITIALIZED);
        format_section(instr);
        instr_stream ~= instr;
      }
      else {
        uvm_fatal(get_full_name(), "The signature_addr is not properly configured!");
      }
    }
  }

  // Generate some dummy writes to xSTATUS/xIE at the beginning of the test to check
  // repeated writes to these CSRs.
  void gen_dummy_csr_write() {
    string[] instr;
    if (cfg.enable_dummy_csr_write) {
      switch (cfg.init_privileged_mode) {
      case privileged_mode_t.MACHINE_MODE:
	instr ~= format("csrr x%0d, 0x%0x", cfg.gpr[0], privileged_reg_t.MSTATUS);
	instr ~= format("csrr x%0d, 0x%0x", cfg.gpr[1], privileged_reg_t.MIE);
	instr ~= format("csrw 0x%0x, x%0d", privileged_reg_t.MSTATUS, cfg.gpr[0]);
	instr ~= format("csrw 0x%0x, x%0d", privileged_reg_t.MIE, cfg.gpr[1]);
	break;
      case privileged_mode_t.SUPERVISOR_MODE:
	instr ~= format("csrr x%0d, 0x%0x", cfg.gpr[0], privileged_reg_t.SSTATUS);
	instr ~= format("csrr x%0d, 0x%0x", cfg.gpr[1], privileged_reg_t.SIE);
	instr ~= format("csrw 0x%0x, x%0d", privileged_reg_t.SSTATUS, cfg.gpr[0]);
	instr ~= format("csrw 0x%0x, x%0d", privileged_reg_t.SIE, cfg.gpr[1]);
	break;
      case privileged_mode_t.USER_MODE:
	static if (!support_umode_trap) {
	  return;
	}
	else {
	  instr ~= format("csrr x%0d, 0x%0x", cfg.gpr[0], privileged_reg_t.USTATUS);
	  instr ~= format("csrr x%0d, 0x%0x", cfg.gpr[1], privileged_reg_t.UIE);
	  instr ~= format("csrw 0x%0x, x%0d", privileged_reg_t.USTATUS, cfg.gpr[0]);
	  instr ~= format("csrw 0x%0x, x%0d", privileged_reg_t.UIE, cfg.gpr[1]);
	  break;
	}
      default:
	uvm_fatal(get_full_name(), "Unsupported boot mode");
      }
      format_section(instr);
      instr_stream ~= instr;
    }
  }

  // Initialize general purpose registers with random value
  void init_gpr() {
    static CstVecDistSolver!(ubvec!DATA_WIDTH) _gpr_solver;
    string str;
    ubvec!DATA_WIDTH reg_val;
    // Init general purpose registers with random values
    for(int i = 0; i < NUM_GPR; i++) {
      if (i.inside(cfg.sp, cfg.tp)) continue;

      if (_gpr_solver is null) {
	_gpr_solver = new CstVecDistSolver!(ubvec!DATA_WIDTH)(null);
	_gpr_solver ~= CstVecDistRange!(ubvec!DATA_WIDTH)(ubvec!DATA_WIDTH(0),
							  ubvec!DATA_WIDTH(0),
							  1, false);
	_gpr_solver ~= CstVecDistRange!(ubvec!DATA_WIDTH)(ubvec!DATA_WIDTH(0x1),
							  ubvec!DATA_WIDTH(0xF),
							  1, false);
	_gpr_solver ~= CstVecDistRange!(ubvec!DATA_WIDTH)(ubvec!DATA_WIDTH(0x10),
							  ubvec!DATA_WIDTH(0xEFFF_FFFF),
							  1, false);
	_gpr_solver ~= CstVecDistRange!(ubvec!DATA_WIDTH)(ubvec!DATA_WIDTH(0x8000_0000),
							  ubvec!DATA_WIDTH(0x8000_0000),
							  1, false);
	_gpr_solver ~= CstVecDistRange!(ubvec!DATA_WIDTH)(ubvec!DATA_WIDTH(0xF000_0000),
							  ubvec!DATA_WIDTH(0xFFFF_FFFF),
							  1, false);
      }
      reg_val = _gpr_solver.urandom();
      str = format("%0sli x%0d, 0x%0x", indent, i, reg_val);
      instr_stream ~= str;
    }
  }

  // Initialize vector general purpose registers
  void init_vec_gpr() {
    int SEW;
    int LMUL;
    int EDIV = 1;
    int len = (ELEN <= XLEN) ? ELEN : XLEN;
    int num_elements = VLEN / len;
    if (!(canFind(supported_isa, riscv_instr_group_t.RVV))) return;
    LMUL = 1;
    SEW = (ELEN <= XLEN) ? ELEN : XLEN;
    instr_stream ~= format("li x%0d, %0d", cfg.gpr[1], cfg.vector_cfg.vl);
    instr_stream ~= format("%svsetvli x%0d, x%0d, e%0d, m%0d, d%0d",
			   indent, cfg.gpr[0], cfg.gpr[1], SEW, LMUL, EDIV);
    instr_stream ~= "vec_reg_init:";

    // Vector registers will be initialized using one of the following three methods
    switch (cfg.vreg_init_method) {
    case vreg_init_method_t.SAME_VALUES_ALL_ELEMS:
      for (int v = 0; v < NUM_VEC_GPR; v++) {
	instr_stream ~= format("%0svmv.v.x v%0d, x%0d", indent, v, v);
      }
      break;
    case vreg_init_method_t.RANDOM_VALUES_VMV:
      for (int v = 0; v < NUM_VEC_GPR; v++) {
	for (int e = 0; e < num_elements; e++) {
	  if (e > 0) instr_stream ~= format("%0svmv.v.v v0, v%0d", indent, v);
	  instr_stream ~= format("%0sli x%0d, 0x%0x",
				 indent, cfg.gpr[0], urandom(0, 2 ^^ SEW));
	  if (v > 0) {
	    instr_stream ~= format("%0svslide1up.vx v%0d, v0, x%0d",
				   indent, v, cfg.gpr[0]);
	  }
	  else {
	    instr_stream ~= format("%0svslide1up.vx v%0d, v1, x%0d",
				   indent, v, cfg.gpr[0]);
	  }
	}
      }
      break;
    case vreg_init_method_t.RANDOM_VALUES_LOAD:
      // Select those memory regions that are big enough for load a vreg
      mem_region_t[] valid_mem_region;
      foreach (region; cfg.mem_region) {
	if (region.size_in_bytes * 8 >= VLEN) valid_mem_region ~= region;
      }
      if (valid_mem_region.length == 0)
	uvm_fatal(get_full_name(), "Couldn't find a memory region big enough to initialize the vector registers");

      for (int v = 0; v < NUM_VEC_GPR; v++) {
	assert (valid_mem_region.length != 0);
	uint region = urandom(0, cast(uint) valid_mem_region.length);
	instr_stream ~= format("%0sla t0, %0s", indent, valid_mem_region[region]);
	instr_stream ~= format("%0svle.v v%0d, (t0)", indent, v);
      }
      break;
    default : break;
    }
  }

  // Initialize floating point general purpose registers
  void init_floating_point_gpr() {
    int int_gpr;
    string str;
    for (int i = 0; i < NUM_FLOAT_GPR; i++) {
      if (canFind( supported_isa, riscv_instr_group_t.RV64D)) {
	if (urandom!bool()) init_floating_point_gpr_with_spf(i);
	else init_floating_point_gpr_with_dpf(i);
      }
      else init_floating_point_gpr_with_spf(i);
    }
    // Initialize rounding mode of FCSR
    str = format("%0sfsrmi %0d", indent, cfg.fcsr_rm);
    instr_stream ~= str;
  }

  // get instructions initialize floating_point_gpr with single precision floating value
  void init_floating_point_gpr_with_spf(int int_floating_gpr) {
    string str;
    ubvec!32 imm = cast(ubvec!32) get_rand_spf_value();
    str = format("%0sli x%0d, %0d", indent, cfg.gpr[0], imm);
    instr_stream ~= str;
    str = format("%0sfmv.w.x f%0d, x%0d", indent, int_floating_gpr, cfg.gpr[0]);
    instr_stream ~= str;
  }

  // get instructions initialize floating_point_gpr with double precision floating value
  void init_floating_point_gpr_with_dpf(int int_floating_gpr) {
    string str;
    ubvec!64 imm = get_rand_dpf_value();
    int int_gpr1 = cfg.gpr[0];
    int int_gpr2 = cfg.gpr[1];

    str = format("%0sli x%0d, %0d", indent, int_gpr1, imm[32..64]);
    instr_stream ~= str;
    // shift to upper 32bits
    for(int i=0 ; i<2 ; ++i) {
      str = format("%0sslli x%0d, x%0d, 16", indent, int_gpr1, int_gpr1);
      instr_stream ~= str;
    }
    str = format("%0sli x%0d, %0d", indent, int_gpr2, imm[0..32]);
    instr_stream ~= str;
    str = format("%0sor x%0d, x%0d, x%0d", indent, int_gpr2, int_gpr2, int_gpr1);
    instr_stream ~= str;
    str = format("%0sfmv.d.x f%0d, x%0d", indent, int_floating_gpr, int_gpr2);
    instr_stream ~= str;
  }

  // get a random single precision floating value
  ubvec!XLEN get_rand_spf_value() {
    ubvec!XLEN value;
    int randint = urandom(0,6);
    switch ( randint) {
    case 0: value = urandom!q{[]}(0x7f80_0000, 0xff80_0000); break;
    case 1: value = urandom!q{[]}(0x7f7f_ffff, 0xff7f_ffff); break;
    case 2: value = urandom!q{[]}(0x0000_0000, 0x8000_0000); break;
    case 3: value = urandom!q{[]}(0x7f80_0001, 0x7fc0_0000); break;
    case 4: value[SINGLE_PRECISION_FRACTION_BITS..31] =
	toubvec!XLEN(urandom(1, 2 ^^ (31-SINGLE_PRECISION_FRACTION_BITS))); break;
    case 5: value[SINGLE_PRECISION_FRACTION_BITS..31] = 0; break;
    default: break;
    }

    return value;
  }

  // get a random double precision floating value
  ubvec!64 get_rand_dpf_value() {
    ubvec!64 value;

    int randint = urandom(0,6);
    switch ( randint) {
    case 0: value = toubvec!64(urandom!q{[]}(0x7ff0_0000_0000_0000, 0xfff0_0000_0000_0000)); break;
    case 1: value = toubvec!64(urandom!q{[]}(0x7fef_ffff_ffff_ffff, 0xffef_ffff_ffff_ffff)); break;
    case 2: value = toubvec!64(urandom!q{[]}(0x0000_0000_0000_0000, 0x8000_0000_0000_0000)); break;
    case 3: value = toubvec!64(urandom!q{[]}(0x7ff0_0000_0000_0001, 0x7ff8_0000_0000_0000)); break;
    case 4: value[DOUBLE_PRECISION_FRACTION_BITS..63] =
	toubvec!64(urandom(1, 2 ^^ (63-SINGLE_PRECISION_FRACTION_BITS))); break;
    case 5: value[DOUBLE_PRECISION_FRACTION_BITS..63] = 0; break;
    default: break;
    }
    return value;
  }

  // Generate "test_done" section, test is finished by an ECALL instruction
  // The ECALL trap handler will handle the clean up procedure before finishing the test.
  void gen_test_done() {
    string str = format_string("test_done:", LABEL_STR_LEN);
    instr_stream ~= str;
    instr_stream ~= (indent ~ "li gp, 1");
    if (cfg.bare_program_mode) {
      instr_stream ~= indent ~ "j write_tohost";
    } else {
      instr_stream ~= indent ~ "ecall";
    }
  }

  // Dump all GPR to the starting point of the program
  // TB can check the GPR value for this memory location to compare with expected value generated
  // by the ISA simulator. If the processor doesn't have a good tracer unit, it might not be
  // possible to compare the GPR value after each instruction execution.
  void gen_register_dump(ref string[] instr) {
    string str;
    // Load base address
    str = format("la x%0d, _start", cfg.gpr[0]);
    instr ~= str;
    // Generate sw/sd instructions
    for(int i = 0; i < 32; i++) {
      if(XLEN == 64) {
        str = format("sd x%0d, %0d(x%0d)", i, i*(XLEN/8), cfg.gpr[0]);
      }
      else {
        str = format("sw x%0d, %0d(x%0d)", i, i*(XLEN/8), cfg.gpr[0]);
      }
      instr ~= str;
    }
  }

  //---------------------------------------------------------------------------------------
  // Privileged mode entering routine
  //---------------------------------------------------------------------------------------

  void pre_enter_privileged_mode(int hart) {
    string[] instr;
    string[] str;
    // Setup kerenal stack pointer
    str ~= format("la x%0d, %0skernel_stack_end", cfg.tp, hart_prefix(hart));
    gen_section(get_label("kernel_sp", hart), str);
    // Setup interrupt and exception delegation
    if (!cfg.no_delegation && (cfg.init_privileged_mode != privileged_mode_t.MACHINE_MODE)) {
      gen_delegation(hart);
    }
    // Setup trap vector register
    trap_vector_init(hart);
    // Setup PMP CSRs
    setup_pmp(hart);
    // Generate PMPADDR write test sequence
    gen_pmp_csr_write(hart);
    // Initialize PTE (link page table based on their real physical address)
    if (cfg.virtual_addr_translation_on) {
      page_table_list.process_page_table(instr);
      gen_section(get_label("process_pt", hart), instr);
    }
    // Setup mepc register, jump to init entry
    setup_epc(hart);
    // Initialization of any implementation-specific custom CSRs
    setup_custom_csrs(hart);
    // Setup initial privilege mode
    gen_privileged_mode_switch_routine(hart);
  }

  void gen_privileged_mode_switch_routine(int hart) {
    privil_seq = riscv_privileged_common_seq.type_id.create("privil_seq");
    foreach (mode; supported_privileged_mode) {
      string[] instr;
      string[] csr_handshake;
      string ret_instr;
      if (mode != cfg.init_privileged_mode) continue;
      uvm_info(get_full_name(), format("Generating privileged mode routing for %0s", mode), UVM_LOW);
      // Enter privileged mode
      privil_seq.cfg = cfg;
      privil_seq.hart = hart;
      privil_seq.randomize();
      privil_seq.enter_privileged_mode(mode, instr);
      if (cfg.require_signature_addr) {
	ret_instr = instr[$-1];
        instr.length -= 1;	// pop_back
        // Want to write the main system CSRs to the testbench before indicating that initialization
        // is complete, for any initial state analysis
        switch (mode) {
	case privileged_mode_t.SUPERVISOR_MODE:
	  gen_signature_handshake(csr_handshake,
				  signature_type_t.WRITE_CSR,
				  core_status_t.INITIALIZED,
				  test_result_t.TEST_FAIL,
				  privileged_reg_t.SSTATUS);
	  gen_signature_handshake(csr_handshake,
				  signature_type_t.WRITE_CSR,
				  core_status_t.INITIALIZED,
				  test_result_t.TEST_FAIL,
				  privileged_reg_t.SIE);
	  break;
	case privileged_mode_t.USER_MODE:
	  gen_signature_handshake(csr_handshake,
				  signature_type_t.WRITE_CSR,
				  core_status_t.INITIALIZED,
				  test_result_t.TEST_FAIL,
				  privileged_reg_t.USTATUS);
	  gen_signature_handshake(csr_handshake,
				  signature_type_t.WRITE_CSR,
				  core_status_t.INITIALIZED,
				  test_result_t.TEST_FAIL,
				  privileged_reg_t.UIE);
	  break;
	default: uvm_info(get_full_name(), format("Unsupported privileged_mode %0s", mode), UVM_LOW);
        }
        // Write M-mode CSRs to testbench by default, as these should be implemented
        gen_signature_handshake(csr_handshake,
				signature_type_t.WRITE_CSR,
				core_status_t.INITIALIZED,
				test_result_t.TEST_FAIL,
				privileged_reg_t.MSTATUS);
        gen_signature_handshake(csr_handshake,
				signature_type_t.WRITE_CSR,
				core_status_t.INITIALIZED,
				test_result_t.TEST_FAIL,
				privileged_reg_t.MIE);
        format_section(csr_handshake);
        instr ~= csr_handshake;
	instr ~= ret_instr;
      }
      instr_stream ~= instr;
    }
  }

  // Setup EPC before entering target privileged mode
  void setup_epc(int hart) {
    import std.conv: to;

    string[] instr;
    string mode_name;
    instr = [format("la x%0d, %0sinit", cfg.gpr[0], hart_prefix(hart))];
    if(cfg.virtual_addr_translation_on) {
      // For supervisor and user mode, use virtual address instead of physical address.
      // Virtual address starts from address 0x0, here only the lower 12 bits are kept
      // as virtual address offset.
      instr ~= format("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 12);
      instr ~= format("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 12);
    }
    mode_name = (cfg.init_privileged_mode).to!string();
    instr ~= format("csrw 0x%0x, x%0d", privileged_reg_t.MEPC, cfg.gpr[0]);
    gen_section(get_label("mepc_setup", hart), instr);
  }

  // Setup PMP CSR configuration
  void setup_pmp(int hart) {
    string[] instr;
    if (support_pmp) {
      cfg.pmp_cfg.setup_pmp();
      cfg.pmp_cfg.gen_pmp_instr([cfg.scratch_reg, cfg.gpr[0]], instr);
      gen_section(get_label("pmp_setup", hart), instr);
    }
  }

  // Generates a directed stream of instructions to write random values to all supported
  // pmpaddr CSRs to test write accessibility.
  // The original CSR values are restored afterwards.
  void gen_pmp_csr_write(int hart) {
    string[] instr;
    if (support_pmp && cfg.pmp_cfg.enable_write_pmp_csr) {
      cfg.pmp_cfg.gen_pmp_write_test([cfg.scratch_reg, cfg.pmp_reg], instr);
      gen_section(get_label("pmp_csr_write_test", hart), instr);
    }
  }

  // Handles creation of a subroutine to initialize any custom CSRs
  void setup_custom_csrs(int hart) {
    string[] instr;
    init_custom_csr(instr);
    gen_section(get_label("custom_csr_setup", hart), instr);
  }

  // This function should be overridden in the riscv_asm_program_gen extended class
  // corresponding to the RTL implementation if it has any custom CSRs defined.
  //
  // All that needs to be done in the overridden function is to manually create
  // the instruction strings to set up any custom CSRs and then to push those strings
  // into the instr queue.
  void init_custom_csr(ref Queue!string instr) {
    instr ~= "nop";
  }

  void init_custom_csr(ref string[] instr) {
    instr ~= "nop";
  }

  //---------------------------------------------------------------------------------------
  // Privileged CSR setup for interrupt and exception handling and delegation
  //---------------------------------------------------------------------------------------

  // Interrupt and exception delegation setting.
  // The lower level exception and interrupt can be delegated to higher level handler.
  void gen_delegation(int hart) {
    gen_delegation_instr(hart,
			 privileged_reg_t.MEDELEG,
			 privileged_reg_t.MIDELEG,
                         cfg.m_mode_exception_delegation,
                         cfg.m_mode_interrupt_delegation);
    if (support_umode_trap) {
      gen_delegation_instr(hart,
			   privileged_reg_t.SEDELEG,
			   privileged_reg_t.SIDELEG,
                           cfg.s_mode_exception_delegation,
                           cfg.s_mode_interrupt_delegation);
    }
  }

  void gen_delegation_instr(int hart,
			    privileged_reg_t edeleg,
			    privileged_reg_t ideleg,
			    bool[exception_cause_t] edeleg_enable,
			    bool[interrupt_cause_t] ideleg_enable) {
    import std.conv: to;
    ubvec!XLEN deleg_val;
    string section_name;
    string[] instr;
    // Exception delegation setup
    foreach (cause, ref enable; edeleg_enable) {
      if (enable) {
        deleg_val |= 1 << cause;
      }
    }
    instr = [format("li x%0d, 0x%0x", cfg.gpr[0], deleg_val),
	     format("csrw 0x%0x, x%0d # %0s", edeleg, cfg.gpr[0], edeleg)];
    // Interrupt delegation setup
    deleg_val = 0;
    foreach (cause, ref enable; ideleg_enable) {
      if (enable) {
        deleg_val |= 1 << cause;
      }
    }
    instr ~= format("li x%0d, 0x%0x", cfg.gpr[0], deleg_val);
    instr ~= format("csrw 0x%0x, x%0d # %0s", ideleg, cfg.gpr[0], ideleg);
    section_name = (edeleg).to!string;
    section_name = section_name.toLower();
    gen_section(get_label(format("%0s_setup", section_name), hart), instr);
  }

  // Setup trap vector - MTVEC, STVEC, UTVEC
  void trap_vector_init(int hart) {
    import std.conv: to;

    string[] instr;
    privileged_reg_t trap_vec_reg;
    string tvec_name;
    foreach(mode; supported_privileged_mode) {
      switch (mode) {
      case privileged_mode_t.MACHINE_MODE:    trap_vec_reg = privileged_reg_t.MTVEC; break;
      case privileged_mode_t.SUPERVISOR_MODE: trap_vec_reg = privileged_reg_t.STVEC; break;
      case privileged_mode_t.USER_MODE:       trap_vec_reg = privileged_reg_t.UTVEC; break;
      default: uvm_info(get_full_name(), format("Unsupported privileged_mode %0s", mode), UVM_LOW);
      }
      // Skip utvec init if trap delegation to u_mode is not supported
      if ((mode == privileged_mode_t.USER_MODE) &&
          !support_umode_trap) continue;
      if (mode < cfg.init_privileged_mode) continue;
      tvec_name = trap_vec_reg.to!string();
      instr ~= format("la x%0d, %0s%0s_handler",
		      cfg.gpr[0], hart_prefix(hart), tvec_name.toLower());
      if (SATP_MODE != satp_mode_t.BARE && mode != privileged_mode_t.MACHINE_MODE) {
        // For supervisor and user mode, use virtual address instead of physical address.
        // Virtual address starts from address 0x0, here only the lower 20 bits are kept
        // as virtual address offset.
        instr ~= format("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 20);
	instr ~= format("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 20);
      }
      instr ~= format("ori x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], cfg.mtvec_mode);
      instr ~= format("csrw 0x%0x, x%0d # %0s",
		      trap_vec_reg, cfg.gpr[0], to!string(trap_vec_reg));
    }
    gen_section(get_label("trap_vec_init", hart), instr);
  }

  //---------------------------------------------------------------------------------------
  // Exception handling routine
  //---------------------------------------------------------------------------------------

  // Trap handling routine
  void gen_all_trap_handler(int hart) {
    string[] instr;
    // If PMP isn't supported, generate the relevant trap handler sections as per usual
    if (!support_pmp) {
      gen_trap_handlers(hart);
      // Ecall handler
      gen_ecall_handler(hart);
      // Instruction fault handler
      gen_instr_fault_handler(hart);
      // Load fault handler
      gen_load_fault_handler(hart);
      // Store fault handler
      gen_store_fault_handler(hart);
    }
    // Ebreak handler
    gen_ebreak_handler(hart);
    // Illegal instruction handler
    gen_illegal_instr_handler(hart);
    // Generate page table fault handling routine
    // Page table fault is always handled in machine mode, as virtual address translation may be
    // broken when page fault happens.
    gen_signature_handshake(instr, signature_type_t.CORE_STATUS, core_status_t.HANDLING_EXCEPTION);
    if(page_table_list !is null) {
      page_table_list.gen_page_fault_handling_routine(instr);
    }
    else {
      instr ~= "nop";
    }
    gen_section(get_label("pt_fault_handler", hart), instr);
  }

  void gen_trap_handlers(int hart) {
    foreach (mode; supported_privileged_mode) {
      if(mode < cfg.init_privileged_mode) continue;
      switch (mode) {
      case privileged_mode_t.MACHINE_MODE:
	gen_trap_handler_section(hart, "m",
				 privileged_reg_t.MCAUSE,
				 privileged_reg_t.MTVEC,
				 privileged_reg_t.MTVAL,
				 privileged_reg_t.MEPC,
				 privileged_reg_t.MSCRATCH,
				 privileged_reg_t.MSTATUS,
				 privileged_reg_t.MIE,
				 privileged_reg_t.MIP);
	break;
      case privileged_mode_t.SUPERVISOR_MODE:
	gen_trap_handler_section(hart, "s",
				 privileged_reg_t.SCAUSE,
				 privileged_reg_t.STVEC,
				 privileged_reg_t.STVAL,
				 privileged_reg_t.SEPC,
				 privileged_reg_t.SSCRATCH,
				 privileged_reg_t.SSTATUS,
				 privileged_reg_t.SIE,
				 privileged_reg_t.SIP);
	break;
      case privileged_mode_t.USER_MODE:
	if (support_umode_trap) {
	  gen_trap_handler_section(hart, "u",
				   privileged_reg_t.UCAUSE,
				   privileged_reg_t.UTVEC,
				   privileged_reg_t.UTVAL,
				   privileged_reg_t.UEPC,
				   privileged_reg_t.USCRATCH,
				   privileged_reg_t.USTATUS,
				   privileged_reg_t.UIE,
				   privileged_reg_t.UIP);
	}
	break;
      default: uvm_fatal(get_full_name(), format("Unsupported privileged_mode %0s", mode));
      }
    }
  }

  // Generate the interrupt and trap handler for different privileged mode.
  // The trap handler checks the xCAUSE to determine the type of the exception and jumps to
  // corresponding exeception handling routine.
  void gen_trap_handler_section(int hart,
				string mode,
				privileged_reg_t cause, privileged_reg_t tvec,
				privileged_reg_t tval, privileged_reg_t epc,
				privileged_reg_t scratch, privileged_reg_t status,
				privileged_reg_t ie, privileged_reg_t ip) {
    import std.conv: to;
    bool is_interrupt = true;
    string tvec_name;
    string[] instr;
    if (cfg.mtvec_mode == mtvec_mode_t.VECTORED) {
      gen_interrupt_vector_table(hart, mode, status, cause, ie, ip, scratch, instr);
    }
    else {
      // Push user mode GPR to kernel stack before executing exception handling, this is to avoid
      // exception handling routine modify user program state unexpectedly
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
      // Checking xStatus can be optional if ISS (like spike) has different implementation of
      // certain fields compared with the RTL processor.
      if (cfg.check_xstatus) {
        instr ~= format("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], status, status);
      }
      instr ~=
	// Use scratch CSR to save a GPR value
	// Check if the exception is caused by an interrupt, if yes, jump to interrupt
	// handler Interrupt is indicated by xCause[XLEN-1]
	[format("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause),
	 format("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN-1),
	 format("bne x%0d, x0, %0s%0smode_intr_handler", cfg.gpr[0], hart_prefix(hart), mode)];
    }
    // The trap handler will occupy one 4KB page, it will be allocated one entry in the page table
    // with a specific privileged mode.
    if (SATP_MODE != satp_mode_t.BARE) {
      instr_stream ~= ".align 12";
    }
    else {
      instr_stream ~= format(".align %d", cfg.tvec_alignment);
    }
    tvec_name = tvec.to!string();
    gen_section(get_label(format("%0s_handler", tvec_name.toLower()), hart), instr);
    // Exception handler
    instr = [];
    if (cfg.mtvec_mode == mtvec_mode_t.VECTORED) {
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    }
    gen_signature_handshake(instr, signature_type_t.CORE_STATUS, core_status_t.HANDLING_EXCEPTION);
    instr ~=
      // The trap is caused by an exception, read back xCAUSE, xEPC to see if these
      // CSR values are set properly. The checking is done by comparing against the log
      // generated by ISA simulator (spike).
      [format("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], epc, epc),
       format("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause),
       // Breakpoint
       format("li x%0d, 0x%0x # BREAKPOINT", cfg.gpr[1], exception_cause_t.BREAKPOINT),
       format("beq x%0d, x%0d, %0sebreak_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       // Check if it's an ECALL exception. Jump to ECALL exception handler
       format("li x%0d, 0x%0x # ECALL_UMODE", cfg.gpr[1], exception_cause_t.ECALL_UMODE),
       format("beq x%0d, x%0d, %0secall_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       format("li x%0d, 0x%0x # ECALL_SMODE", cfg.gpr[1], exception_cause_t.ECALL_SMODE),
       format("beq x%0d, x%0d, %0secall_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       format("li x%0d, 0x%0x # ECALL_MMODE", cfg.gpr[1], exception_cause_t.ECALL_MMODE),
       format("beq x%0d, x%0d, %0secall_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       // Page table fault or access fault conditions
       format("li x%0d, 0x%0x", cfg.gpr[1], exception_cause_t.INSTRUCTION_ACCESS_FAULT),
       format("beq x%0d, x%0d, %0sinstr_fault_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       format("li x%0d, 0x%0x", cfg.gpr[1], exception_cause_t.LOAD_ACCESS_FAULT),
       format("beq x%0d, x%0d, %0sload_fault_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       format("li x%0d, 0x%0x", cfg.gpr[1], exception_cause_t.STORE_AMO_ACCESS_FAULT),
       format("beq x%0d, x%0d, %0sstore_fault_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       format("li x%0d, 0x%0x", cfg.gpr[1], exception_cause_t.INSTRUCTION_PAGE_FAULT),
       format("beq x%0d, x%0d, %0spt_fault_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       format("li x%0d, 0x%0x", cfg.gpr[1], exception_cause_t.LOAD_PAGE_FAULT),
       format("beq x%0d, x%0d, %0spt_fault_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       format("li x%0d, 0x%0x", cfg.gpr[1], exception_cause_t.STORE_AMO_PAGE_FAULT),
       format("beq x%0d, x%0d, %0spt_fault_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       // Illegal instruction exception
       format("li x%0d, 0x%0x # ILLEGAL_INSTRUCTION", cfg.gpr[1], exception_cause_t.ILLEGAL_INSTRUCTION),
       format("beq x%0d, x%0d, %0sillegal_instr_handler",
	      cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
       // Skip checking tval for illegal instruction as it's implementation specific
       format("csrr x%0d, 0x%0x # %0s", cfg.gpr[1], tval, tval),
       // use JALR to jump to test_done.
       format("1: la x%0d, test_done", cfg.scratch_reg),
       format("jalr x1, x%0d, 0", cfg.scratch_reg)
       ];
    gen_section(get_label(format("%0smode_exception_handler", mode), hart), instr);
  }

  // Generate for interrupt vector table
  void gen_interrupt_vector_table(int              hart,
				  string           mode,
				  privileged_reg_t status,
				  privileged_reg_t cause,
				  privileged_reg_t ie,
				  privileged_reg_t ip,
				  privileged_reg_t scratch,
				  ref string[]     instr) {
    import std.conv: to;
    // In vector mode, the BASE address is shared between interrupt 0 and exception handling.
    // When vectored interrupts are enabled, interrupt cause 0, which corresponds to user-mode
    // software interrupts, are vectored to the same location as synchronous exceptions. This
    // ambiguity does not arise in practice, since user-mode software interrupts are either
    // disabled or delegated
    instr ~= ".option norvc;" ~ format("j %0s%0smode_exception_handler", hart_prefix(hart), mode);
    // Redirect the interrupt to the corresponding interrupt handler
    for (int i = 1; i < max_interrupt_vector_num; i++) {
      instr ~= format("j %0s%0smode_intr_vector_%0d", hart_prefix(hart), mode, i);
    }
    if (!cfg.disable_compressed_instr) {
      instr ~= ".option rvc;";
    }
    for (int i = 1; i < max_interrupt_vector_num; i++) {
      string[] intr_handler;
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, intr_handler);
      gen_signature_handshake(intr_handler, signature_type_t.CORE_STATUS,
                              core_status_t.HANDLING_IRQ);
      intr_handler ~= [format("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause),
		       // Terminate the test if xCause[31] != 0 (indicating exception)
		       format("srli x%0d, x%0d, 0x%0x", cfg.gpr[0], cfg.gpr[0], XLEN-1),
		       format("beqz x%0d, 1f", cfg.gpr[0])];
      gen_signature_handshake(intr_handler,
			      signature_type_t.WRITE_CSR,
			      core_status_t.INITIALIZED,
			      test_result_t.TEST_FAIL,
			      status);
      gen_signature_handshake(intr_handler,
			      signature_type_t.WRITE_CSR,
			      core_status_t.INITIALIZED,
			      test_result_t.TEST_FAIL,
			      cause);
      gen_signature_handshake(intr_handler,
			      signature_type_t.WRITE_CSR,
			      core_status_t.INITIALIZED,
			      test_result_t.TEST_FAIL,
			      ie);
      gen_signature_handshake(intr_handler,
			      signature_type_t.WRITE_CSR,
			      core_status_t.INITIALIZED,
			      test_result_t.TEST_FAIL,
			      ip);
      // Jump to commmon interrupt handling routine
      intr_handler ~=
	[format("j %0s%0smode_intr_handler", hart_prefix(hart), mode),
	 format("1: la x%0d, test_done", cfg.scratch_reg),
	 format("jalr x0, x%0d, 0", cfg.scratch_reg)];

      gen_section(get_label(format("%0smode_intr_vector_%0d", mode, i), hart), intr_handler);
    }
  }

  // ECALL trap handler
  // It does some clean up like dump GPRs before communicating with host to terminate the test.
  // User can extend this function if some custom clean up routine is needed.
  void gen_ecall_handler(int hart) {
    string[] instr;
    dump_perf_stats(instr);
    gen_register_dump(instr);
    instr ~= format("la x%0d, write_tohost", cfg.scratch_reg);
    instr ~= format("jalr x0, x%0d, 0", cfg.scratch_reg);
    gen_section(get_label("ecall_handler", hart), instr);
  }

  // Ebreak trap handler
  // When breakpoint exception happens, epc will be written with ebreak instruction
  // itself. Add epc by 4 and resume execution.
  // Note the breakpoint could be triggered by a C.EBREAK instruction, the generated program
  // guarantees that epc + 4 is a valid instruction boundary
  // TODO: Support random operations in debug mode
  // TODO: Support ebreak exception delegation
  // TODO: handshake the correct Xcause CSR based on delegation privil. mode
  void gen_ebreak_handler(int hart) {
    string[] instr;
    gen_signature_handshake(instr, signature_type_t.CORE_STATUS, core_status_t.EBREAK_EXCEPTION);
    gen_signature_handshake(instr,
			    signature_type_t.WRITE_CSR,
			    core_status_t.INITIALIZED,
			    test_result_t.TEST_FAIL,
			    privileged_reg_t.MCAUSE);
    instr ~= [format("csrr  x%0d, 0x%0x", cfg.gpr[0], privileged_reg_t.MEPC),
	      format("addi  x%0d, x%0d, 4", cfg.gpr[0], cfg.gpr[0]),
	      format("csrw  0x%0x, x%0d", privileged_reg_t.MEPC, cfg.gpr[0])];
    pop_gpr_from_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr ~= "mret";
    gen_section(get_label("ebreak_handler", hart), instr);
  }

  // Illegal instruction handler
  // Note: Save the illegal instruction to MTVAL is optional in the spec, and mepc could be
  // a virtual address that cannot be used in machine mode handler. As a result, there's no way to
  // know the illegal instruction is compressed or not. This hanlder just simply adds the PC by
  // 4 and resumes execution. The way that the illegal instruction is injected guarantees that
  // PC + 4 is a valid instruction boundary.
  // TODO: handshake the corret Xcause CSR based on delegation setup
  void gen_illegal_instr_handler(int hart) {
    string[] instr;
    gen_signature_handshake(instr, signature_type_t.CORE_STATUS, core_status_t.ILLEGAL_INSTR_EXCEPTION);
    gen_signature_handshake(instr,
			    signature_type_t.WRITE_CSR,
			    core_status_t.INITIALIZED,
			    test_result_t.TEST_FAIL,
			    privileged_reg_t.MCAUSE);
    instr ~= [format("csrr  x%0d, 0x%0x", cfg.gpr[0], privileged_reg_t.MEPC),
	      format("addi  x%0d, x%0d, 4", cfg.gpr[0], cfg.gpr[0]),
	      format("csrw  0x%0x, x%0d", privileged_reg_t.MEPC, cfg.gpr[0])];
    pop_gpr_from_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr ~= "mret";
    gen_section(get_label("illegal_instr_handler", hart), instr);
  }

  // TODO: handshake correct csr based on delegation
  void gen_instr_fault_handler(int hart) {
    string[] instr;
    riscv_reg_t[6] regs;

    gen_signature_handshake(instr, signature_type_t.CORE_STATUS, core_status_t.INSTR_FAULT_EXCEPTION);
    gen_signature_handshake(instr, signature_type_t.WRITE_CSR, core_status_t.INITIALIZED,
			    test_result_t.TEST_FAIL, privileged_reg_t.MCAUSE);
    if (cfg.pmp_cfg.enable_pmp_exception_handler) {
      cfg.pmp_cfg.gen_pmp_exception_routine(cfg.gpr ~ cfg.scratch_reg ~ cfg.pmp_reg,
                                            exception_cause_t.INSTRUCTION_ACCESS_FAULT,
                                            instr);
    }
    pop_gpr_from_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr ~= "mret";
    gen_section(get_label("instr_fault_handler", hart), instr);
  }

  // TODO: handshake correct csr based on delegation
  void gen_load_fault_handler(int hart) {
    string[] instr;
    gen_signature_handshake(instr, signature_type_t.CORE_STATUS, core_status_t.LOAD_FAULT_EXCEPTION);
    gen_signature_handshake(instr,
			    signature_type_t.WRITE_CSR,
			    core_status_t.INITIALIZED,
			    test_result_t.TEST_FAIL,
			    privileged_reg_t.MCAUSE);
    if (cfg.pmp_cfg.enable_pmp_exception_handler) {
      cfg.pmp_cfg.gen_pmp_exception_routine(cfg.gpr ~ cfg.scratch_reg ~ cfg.pmp_reg,
                                            exception_cause_t.LOAD_ACCESS_FAULT,
                                            instr);
    }
    pop_gpr_from_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr ~= "mret";
    gen_section(get_label("load_fault_handler", hart), instr);
  }

  // TODO: handshake correct csr based on delegation
  void gen_store_fault_handler(int hart) {
    string[] instr;
    gen_signature_handshake(instr, signature_type_t.CORE_STATUS, core_status_t.STORE_FAULT_EXCEPTION);
    gen_signature_handshake(instr,
			    signature_type_t.WRITE_CSR,
			    core_status_t.INITIALIZED,
			    test_result_t.TEST_FAIL,
			    privileged_reg_t.MCAUSE);
    if (cfg.pmp_cfg.enable_pmp_exception_handler) {
      cfg.pmp_cfg.gen_pmp_exception_routine(cfg.gpr ~ cfg.scratch_reg ~ cfg.pmp_reg,
                                            exception_cause_t.STORE_AMO_ACCESS_FAULT,
                                            instr);
    }
    pop_gpr_from_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr ~= "mret";
    gen_section(get_label("store_fault_handler", hart), instr);
  }

  //---------------------------------------------------------------------------------------
  // Page table setup
  //---------------------------------------------------------------------------------------

  // Create page table if virtual address translation is supported.
  // The page is created based on the address translation mode - SV32, SV39, SV48
  // Right now only the lowest level 4KB page table is configured as leaf page table entry (PTE),
  // all the other super pages are link PTE.
  void create_page_table(int hart) {
    string[] instr;
    if (cfg.virtual_addr_translation_on) {
      page_table_list = riscv_page_table_list!(SATP_MODE).type_id.create("page_table_list");
      page_table_list.cfg = cfg;
      page_table_list.create_page_table_list();
      page_table_list.enable_exception = cfg.enable_page_table_exception;
      uvm_info(get_full_name(),
	       format("Randomizing page tables, totally %0d page tables, mode = %0s",
		      page_table_list.page_table.length, cfg.init_privileged_mode), UVM_LOW);
      page_table_list.privileged_mode = cfg.init_privileged_mode;
      page_table_list.randomize();
      page_table_list.randomize_page_table();
      uvm_info(get_full_name(), "Finished creating page tables", UVM_LOW);
    }
  }

  // Generate the page table section of the program
  // The page table is generated as a group of continuous 4KB data sections.
  void gen_page_table_section(int hart) {
    string[] page_table_section;
    if (page_table_list !is null) {
      if (cfg.use_push_data_section) {
        instr_stream ~= format(".pushsection .%0spage_table,\"aw\",@progbits;",
			       hart_prefix(hart));
      }
      else {
        instr_stream ~= format(".section .%0spage_table,\"aw\",@progbits;",
			       hart_prefix(hart));
      }
      foreach(table; page_table_list.page_table) {
        table.gen_page_table_section(page_table_section);
        instr_stream ~= page_table_section;
      }
      if (cfg.use_push_data_section) {
        instr_stream ~= ".popsection;";
      }
    }
  }

  // Only extend this function if the core utilizes a PLIC for handling interrupts
  // In this case, the core will write to a specific location as the response to the interrupt, and
  // external PLIC unit can detect this response and process the interrupt clean up accordingly.
  void gen_plic_section(ref string[] interrupt_handler_instr) {
    // Utilize the memory mapped handshake scheme to signal the testbench that the interrupt
    // handling has been completed and we are about to xRET out of the handler
    gen_signature_handshake(interrupt_handler_instr,
			    signature_type_t.CORE_STATUS,
			    core_status_t.FINISHED_IRQ);
  }

  void gen_plic_section(ref Queue!string interrupt_handler_instr) {
    // Utilize the memory mapped handshake scheme to signal the testbench that the interrupt
    // handling has been completed and we are about to xRET out of the handler
    gen_signature_handshake(interrupt_handler_instr,
			    signature_type_t.CORE_STATUS,
			    core_status_t.FINISHED_IRQ);
  }

  // Interrupt handler routine
  void gen_interrupt_handler_section(privileged_mode_t mode, int hart){
    string mode_prefix;
    string ls_unit;
    privileged_reg_t status, ip, ie, scratch;
    string[] interrupt_handler_instr;
    ls_unit = (XLEN == 32) ? "w" : "d";
    if (mode < cfg.init_privileged_mode) return;
    if (mode == privileged_mode_t.USER_MODE && !support_umode_trap) return;
    switch (mode) {
    case privileged_mode_t.MACHINE_MODE:
      mode_prefix = "m";
      status = privileged_reg_t.MSTATUS;
      ip = privileged_reg_t.MIP;
      ie = privileged_reg_t.MIE;
      scratch = privileged_reg_t.MSCRATCH;
      break;
    case  privileged_mode_t.SUPERVISOR_MODE:
      mode_prefix = "s";
      status = privileged_reg_t.SSTATUS;
      ip = privileged_reg_t.SIP;
      ie = privileged_reg_t.SIE;
      scratch = privileged_reg_t.SSCRATCH;
      break;
    case  privileged_mode_t.USER_MODE:
      mode_prefix = "u";
      status = privileged_reg_t.USTATUS;
      ip = privileged_reg_t.UIP;
      ie = privileged_reg_t.UIE;
      scratch = privileged_reg_t.USCRATCH;
      break;
    default: uvm_fatal(get_full_name(), format("Unsupported mode: %0s", mode));
    }
    // If nested interrupts are enabled, set xSTATUS.xIE in the interrupt handler
    // to re-enable interrupt handling capabilities
    if (cfg.enable_nested_interrupt) {
      interrupt_handler_instr ~= format("csrr x%0d, 0x%0x", cfg.gpr[0], scratch);
      interrupt_handler_instr ~= format("bgtz x%0d, 1f", cfg.gpr[0]);
      interrupt_handler_instr ~= format("csrwi 0x%0x, 0x1", scratch);
      switch (status) {
      case privileged_reg_t.MSTATUS:
	interrupt_handler_instr ~= format("csrsi 0x%0x, 0x%0x", status, 8);
	break;
      case  privileged_reg_t.SSTATUS:
	interrupt_handler_instr ~= format("csrsi 0x%0x, 0x%0x", status, 2);
	break;
      case privileged_reg_t.USTATUS:
	interrupt_handler_instr ~= format("csrsi 0x%0x, 0x%0x", status, 1);
	break;
      default: uvm_fatal(get_full_name(), format("Unsupported status %0s", status));
      }
      interrupt_handler_instr ~= format("1: csrwi 0x%0x,0", scratch);
    }
    // Read back interrupt related privileged CSR
    // The value of these CSR are checked by comparing with spike simulation result.
    interrupt_handler_instr ~= [format("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], status, status),
				format("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], ie, ie),
				format("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], ip, ip),
				// Clean all the pending interrupt
				format("csrrc x%0d, 0x%0x, x%0d # %0s;",
				       cfg.gpr[0], ip, cfg.gpr[0], ip)];
    gen_plic_section(interrupt_handler_instr);
    // Restore user mode GPR value from kernel stack before return
    pop_gpr_from_kernel_stack(status, scratch, cfg.mstatus_mprv,
                              cfg.sp, cfg.tp, interrupt_handler_instr);
    interrupt_handler_instr ~= format("%0sret;", mode_prefix);
    if (SATP_MODE != satp_mode_t.BARE) {
      // The interrupt handler will use one 4KB page
      instr_stream ~= ".align 12";
    }
    else {
      instr_stream ~= ".align 2";
    }
    gen_section(get_label(format("%0smode_intr_handler", mode_prefix), hart),
                interrupt_handler_instr);
  }

  //---------------------------------------------------------------------------------------
  // Helper functions
  //---------------------------------------------------------------------------------------

  // Format a code section, without generating it
  void format_section(ref Queue!string instr) {
    string prefix = format_string(" ", LABEL_STR_LEN);
    foreach (ii; instr) {
      ii = prefix ~ ii;
    }
  }

  void format_section(ref string[] instr) {
    string prefix = format_string(" ", LABEL_STR_LEN);
    foreach (ii; instr) {
      ii = prefix ~ ii;
    }
  }

  // Generate a code section
  void gen_section(string label, Queue!string instr) {
    string str;
    if (label != "") {
      str = format_string(format("%0s:", label), LABEL_STR_LEN);
      instr_stream ~= str;
    }
    foreach (ii; instr) {
      str = indent ~ ii;
      instr_stream ~= str;
    }
    instr_stream ~= "";
  }

  void gen_section(string label, string[] instr) {
    string str;
    if(label != "") {
      str = format_string(format("%0s:", label), LABEL_STR_LEN);
      instr_stream ~= str;
    }
    foreach(i; instr) {
      str = indent ~ i;
      instr_stream ~= str;
    }
    instr_stream ~= "";
  }

  // Dump performance CSRs if applicable
  void dump_perf_stats(ref string[] instr) {
    foreach(icsr; implemented_csr) {
      if (icsr >= privileged_reg_t.MCYCLE && icsr <= privileged_reg_t.MHPMCOUNTER31H) {
        gen_signature_handshake(instr,
				signature_type_t.WRITE_CSR,
				core_status_t.INITIALIZED,
				test_result_t.TEST_FAIL,
				icsr);
      }
    }
  }

  // Write the generated program to a file
  void gen_test_file(string test_name) {
    import std.stdio: File;
    import std.path: dirName;
    import std.file: mkdirRecurse;
    //int fd;
    mkdirRecurse(dirName(test_name));
    auto fd = File(test_name,"w");
    foreach (instr; instr_stream) {
      fd.writeln(instr);
    }
    // $fclose(fd);
    uvm_info(get_full_name(), format("%0s is generated", test_name), UVM_LOW);
  }

  // Helper function to generate the proper sequence of handshake instructions
  // to signal the testbench (see riscv_signature_pkg.sv)
  void gen_signature_handshake(ref string[] instr,
			       in signature_type_t signature_type,
			       core_status_t core_status = core_status_t.INITIALIZED,
			       test_result_t test_result = test_result_t.TEST_FAIL,
			       privileged_reg_t csr = privileged_reg_t.MSCRATCH,
			       string addr_label = "") {
    if (cfg.require_signature_addr) {
      string[] str;
      str = [format("li x%0d, 0x%0h", cfg.gpr[1], cfg.signature_addr)];
      instr ~= str;
      switch (signature_type) {
	// A single data word is written to the signature address.
	// Bits [7:0] contain the signature_type of CORE_STATUS, and the upper
	// XLEN-8 bits contain the core_status_t data.
      case signature_type_t.CORE_STATUS:
	str = [format("li x%0d, 0x%0h", cfg.gpr[0], core_status),
	       format("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
	       format("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
		      cfg.gpr[0], signature_type),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])];
	instr ~= str;
	break;
	// A single data word is written to the signature address.
	// Bits [7:0] contain the signature_type of TEST_RESULT, and the upper
	// XLEN-8 bits contain the test_result_t data.
      case signature_type_t.TEST_RESULT:
	str = [format("li x%0d, 0x%0h", cfg.gpr[0], test_result),
	       format("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
	       format("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
		      cfg.gpr[0], signature_type),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])];
	instr ~= str;
	break;
	// The first write to the signature address contains just the
	// signature_type of WRITE_GPR.
	// It is followed by 32 consecutive writes to the signature address,
	// each writing the data contained in one GPR, starting from x0 as the
	// first write, and ending with x31 as the 32nd write.
      case signature_type_t.WRITE_GPR:
	str = [format("li x%0d, 0x%0h", cfg.gpr[0], signature_type),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])];
	instr ~= str;
	for (int i = 0; i < 32; i++) {
	  str = [format("sw x%0x, 0(x%0d)", i, cfg.gpr[1])];
	  instr ~= str;
	}
	break;
	// The first write to the signature address contains the
	// signature_type of WRITE_CSR in bits [7:0], and the CSR address in
	// the upper XLEN-8 bits.
	// It is followed by a second write to the signature address,
	// containing the data stored in the specified CSR.
      case signature_type_t.WRITE_CSR:
	if (!(canFind(implemented_csr, csr))) {
	  return;
	}
	str = [format("li x%0d, 0x%0h", cfg.gpr[0], csr),
	       format("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
	       format("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
		      cfg.gpr[0], signature_type),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1]),
	       format("csrr x%0d, 0x%0h", cfg.gpr[0], csr),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])];
	instr ~= str;
	break;
      default:
	uvm_fatal(get_full_name(), "signature_type is not defined");
      }
    }
  }

  void gen_signature_handshake(ref Queue!string instr,
			       in signature_type_t signature_type,
			       core_status_t core_status = core_status_t.INITIALIZED,
			       test_result_t test_result = test_result_t.TEST_FAIL,
			       privileged_reg_t csr = privileged_reg_t.MSCRATCH,
			       string addr_label = "") {
    if (cfg.require_signature_addr) {
      Queue!string str;
      str = [format("li x%0d, 0x%0h", cfg.gpr[1], cfg.signature_addr)];
      instr = instr ~ str;
      switch (signature_type) {
	// A single data word is written to the signature address.
	// Bits [7:0] contain the signature_type of CORE_STATUS, and the upper
	// XLEN-8 bits contain the core_status_t data.
      case signature_type_t.CORE_STATUS:
	str = [format("li x%0d, 0x%0h", cfg.gpr[0], core_status),
	       format("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
	       format("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
		      cfg.gpr[0], signature_type),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])];
	instr = instr ~ str;
	break;
	// A single data word is written to the signature address.
	// Bits [7:0] contain the signature_type of TEST_RESULT, and the upper
	// XLEN-8 bits contain the test_result_t data.
      case signature_type_t.TEST_RESULT:
	str = [format("li x%0d, 0x%0h", cfg.gpr[0], test_result),
	       format("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
	       format("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
		      cfg.gpr[0], signature_type),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])];
	instr = instr ~ str;
	break;
	// The first write to the signature address contains just the
	// signature_type of WRITE_GPR.
	// It is followed by 32 consecutive writes to the signature address,
	// each writing the data contained in one GPR, starting from x0 as the
	// first write, and ending with x31 as the 32nd write.
      case signature_type_t.WRITE_GPR:
	str = [format("li x%0d, 0x%0h", cfg.gpr[0], signature_type),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])];
	instr = instr ~ str;
	for(int i = 0; i < 32; i++) {
	  str = [format("sw x%0x, 0(x%0d)", i, cfg.gpr[1])];
	  instr = instr ~ str;
	}
	break;
	// The first write to the signature address contains the
	// signature_type of WRITE_CSR in bits [7:0], and the CSR address in
	// the upper XLEN-8 bits.
	// It is followed by a second write to the signature address,
	// containing the data stored in the specified CSR.
      case signature_type_t.WRITE_CSR:
	if (!(canFind(implemented_csr, csr))) {
	  return;
	}
	str = [format("li x%0d, 0x%0h", cfg.gpr[0], csr),
	       format("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
	       format("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
		      cfg.gpr[0], signature_type),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1]),
	       format("csrr x%0d, 0x%0h", cfg.gpr[0], csr),
	       format("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])];
	instr = instr ~ str;
	break;
      default:
	uvm_fatal(get_full_name(), "signature_type is not defined");
      }
    }
  }

  //---------------------------------------------------------------------------------------
  // Inject directed instruction stream
  //---------------------------------------------------------------------------------------

  void add_directed_instr_stream(string name, uint  ratio) {
    directed_instr_stream_ratio[name] = ratio;
    uvm_info(get_full_name(), format("Adding directed instruction stream:%0s ratio:%0d/1000", name, ratio),
	     UVM_LOW);
  }

  void get_directed_instr_stream() {
    import std.conv: to;
    string args, val;
    string stream_name_opts, stream_freq_opts;
    string stream_name;
    int stream_freq;
    string[] opts;
    CommandLine cmdl = new CommandLine();
    for (int i=0; i<cfg.max_directed_instr_stream_seq; i++) {
      args = format("directed_instr_%0d=", i);
      stream_name_opts = format("stream_name_%0d=", i);
      stream_freq_opts = format("stream_freq_%0d=", i);

      if (cmdl.plusArgs(args ~ "%s", val)) {
	uvm_string_split(val, ',', opts);
	if (opts.length != 2) {
	  uvm_fatal(get_full_name(),
		    format("Incorrect directed instruction format : %0s, expect: name,ratio", val));
	}
	else {
	  add_directed_instr_stream(opts[0], opts[1].to!int());
	}
      }
      else if (cmdl.plusArgs(stream_name_opts ~ "%s", stream_name) &&
	       cmdl.plusArgs(stream_freq_opts ~ "%d", stream_freq)) {
	add_directed_instr_stream(stream_name, stream_freq);
      }
    }
  }

  // Generate directed instruction stream based on the ratio setting
  void generate_directed_instr_stream(in int hart,
				      in string label,
				      in uint original_instr_cnt,
				      in uint  min_insert_cnt,
				      in bool kernel_mode,
				      out riscv_instr_stream[] instr_stream) {
    uvm_object object_h;
    uint  instr_insert_cnt;
    uint  idx;
    uvm_coreservice_t coreservice = uvm_coreservice_t.get();
    uvm_factory factory = coreservice.get_factory();
    if (cfg.no_directed_instr) return;
    foreach (instr_stream_name, ref ratio; directed_instr_stream_ratio) {
      instr_insert_cnt = original_instr_cnt * ratio / 1000;
      if(instr_insert_cnt <= min_insert_cnt) {
        instr_insert_cnt = min_insert_cnt;
      }
      uvm_info(get_full_name(), format("Insert directed instr stream %0s %0d/%0d times",
				       instr_stream_name, instr_insert_cnt, original_instr_cnt), UVM_LOW);
      for (int i = 0; i < instr_insert_cnt; i++) {
        string name = format("%0s_%0d", instr_stream_name, i);
        object_h = factory.create_object_by_name(instr_stream_name, get_full_name(), name);
        if (object_h is null) {
          uvm_fatal(get_full_name(), format("Cannot create instr stream %0s", name));
        }

	riscv_rand_instr_stream new_instr_stream = cast(riscv_rand_instr_stream) object_h;
        if (new_instr_stream !is null) {
	  assert (cfg !is null);
          new_instr_stream.cfg = cfg;
          new_instr_stream.hart = hart;
          new_instr_stream.label = format("%0s_%0d", label, idx);
          new_instr_stream.kernel_mode = kernel_mode;
          new_instr_stream.randomize();
          instr_stream ~= new_instr_stream;
        }
	else {
          uvm_fatal(get_full_name(), format("Cannot cast instr stream %0s", name));
        }
        idx += 1;
      }
    }
    instr_stream.shuffle();
  }

  //---------------------------------------------------------------------------------------
  // Generate the debug ROM, and any related programs
  //---------------------------------------------------------------------------------------

  void gen_debug_rom(int hart) {
    uvm_info(get_full_name(), "Creating debug ROM", UVM_LOW);
    debug_rom = riscv_asm_program_gen.type_id.create("debug_rom", null,
						     "uvm_test_top" ~ "." ~ get_full_name());
    debug_rom.cfg = cfg;
    debug_rom.hart = hart;
    debug_rom.gen_program();
    instr_stream ~= debug_rom.instr_stream;
  }

  //---------------------------------------------------------------------------------------
  // Vector extension generation
  //---------------------------------------------------------------------------------------

  void randomize_vec_gpr_and_csr() {
    string lmul;
    if (!(canFind(supported_isa, riscv_instr_group_t.RVV ) )) return;
    instr_stream ~= indent ~ format("csrwi vxsat, %0d", cfg.vector_cfg.vxsat);
    instr_stream ~= indent ~ format("csrwi vxrm, %0d", cfg.vector_cfg.vxrm);
    init_vec_gpr(); // GPR init uses a temporary SEW/LMUL setting before the final value set below.
    instr_stream ~= format("li x%0d, %0d", cfg.gpr[1], cfg.vector_cfg.vl);
    if ((cfg.vector_cfg.vtype.vlmul > 1) && (cfg.vector_cfg.vtype.fractional_lmul)) {
      lmul = format("mf%0d", cfg.vector_cfg.vtype.vlmul);
    }
    else {
      lmul = format("m%0d", cfg.vector_cfg.vtype.vlmul);
    }
    instr_stream ~= format("%svsetvli x%0d, x%0d, e%0d, m%0d, d%0d",
			   indent,
			   cfg.gpr[0],
			   cfg.gpr[1],
			   cfg.vector_cfg.vtype.vsew,
			   lmul,
			   cfg.vector_cfg.vtype.vediv);
  }

}
