/*
 * Copyright 2018 Google LLC
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

//-----------------------------------------------------------------------------
// RISC-V assembly program generator configuration class
//-----------------------------------------------------------------------------
module riscv.gen.riscv_instr_gen_config;

import riscv.gen.riscv_instr_pkg: data_pattern_t, vreg_init_method_t, exception_cause_t,
  interrupt_cause_t, privileged_mode_t, mtvec_mode_t, f_rounding_mode_t, riscv_reg_t,
  mem_region_t, privileged_reg_t, riscv_instr_category_t, b_ext_group_t,
  riscv_instr_group_t, get_int_arg_value, get_bool_arg_value, get_hex_arg_value,
  cmdline_enum_processor, satp_mode_t;

import riscv.gen.riscv_instr_registry: riscv_instr_registry;
import riscv.gen.isa.riscv_instr_register: register_isa;

import riscv.gen.target: NUM_HARTS, XLEN, supported_privileged_mode, supported_isa,
  SATP_MODE, implemented_csr, support_sfence, support_debug_mode, supported_interrupt_mode;
import riscv.gen.riscv_pmp_cfg: riscv_pmp_cfg;
import riscv.gen.riscv_vector_cfg: riscv_vector_cfg;

import std.traits: EnumMembers;
import std.algorithm: canFind;

import std.string: format, toUpper, toLower, strip;
import std.conv: to;

import esdl.base.cmdl: CommandLine;
import esdl.data.bvec: ubvec, toBit, toubvec, clog2;
import esdl.rand: constraint, rand;

import uvm;


class riscv_instr_gen_config: uvm_object
{

  mixin uvm_object_utils;

  //-----------------------------------------------------------------------------
  // Random instruction generation settings
  //-----------------------------------------------------------------------------

  // Instruction count of the main program
  @rand @UVM_DEFAULT int               main_program_instr_cnt;

  // Instruction count of each sub-program
  @rand @UVM_DEFAULT int[]             sub_program_instr_cnt;

  // Instruction count of the debug rom
  @rand @UVM_DEFAULT int               debug_program_instr_cnt;

  // Instruction count of debug sub-programs
  @rand int[]             debug_sub_program_instr_cnt;

  // Pattern of data section: RAND_DATA, ALL_ZERO, INCR_VAL
  @rand @UVM_DEFAULT data_pattern_t    data_page_pattern;

  // Initialization of the vregs
  // SAME_VALUES_ALL_ELEMS - Using vmv.v.x to fill all the elements of the vreg with the same value as the one in the GPR selected
  // RANDOM_VALUES_VMV     - Using vmv.v.x + vslide1up.vx to randomize the contents of each vector element
  // RANDOM_VALUES_LOAD    - Using vle.v, same approach as RANDOM_VALUES_VMV but more efficient for big VLEN
  vreg_init_method_t      vreg_init_method = vreg_init_method_t.RANDOM_VALUES_VMV;

  // Associate array for delegation configuration for each exception and interrupt
  // When the bit is 1, the corresponding delegation is enabled.
  @rand bool[exception_cause_t]              m_mode_exception_delegation;
  @rand bool[exception_cause_t]              s_mode_exception_delegation;
  @rand bool[interrupt_cause_t]              m_mode_interrupt_delegation;
  @rand bool[interrupt_cause_t]              s_mode_interrupt_delegation;

  // Priviledged mode after boot
  @rand @UVM_DEFAULT privileged_mode_t init_privileged_mode;

  @rand ubvec!(XLEN)     mstatus;
  @rand ubvec!(XLEN)     mie;
  @rand ubvec!(XLEN)     sstatus;
  @rand ubvec!(XLEN)     sie;
  @rand ubvec!(XLEN)     ustatus;
  @rand ubvec!(XLEN)     uie;

  // Key fields in xSTATUS
  // Memory protection bits
  @rand bool             mstatus_mprv;
  @rand bool             mstatus_mxr;
  @rand bool             mstatus_sum;
  @rand bool             mstatus_tvm;
  @rand ubvec!2		 mstatus_fs;
  @rand ubvec!2          mstatus_vs;
  @rand mtvec_mode_t     mtvec_mode;

  // TVEC alignment
  // This value is the log_2 of the byte-alignment of TVEC.BASE field
  // As per RISC-V privileged spec, default will be set to 2 (4-byte aligned)
  @rand @UVM_DEFAULT int              tvec_alignment = 2;

  // Floating point rounding mode
  @rand f_rounding_mode_t fcsr_rm;

  // Enable sfence.vma instruction
  @rand bool              enable_sfence;

  // Reserved register
  // Reserved for various hardcoded routines
  @rand riscv_reg_t[4]    gpr;
  // Used by any DCSR operations inside of the debug rom
  // Also used by the PMP generation.
  @rand riscv_reg_t       scratch_reg;
  // Reg used exclusively by the PMP exception handling routine.
  // Can overlap with the other GPRs used in the random generation,
  // as PMP exception handler is hardcoded and does not include any
  // random instructions.
  @rand riscv_reg_t       pmp_reg;
  // Use a random register for stack pointer/thread pointer
  @rand @UVM_DEFAULT riscv_reg_t       sp;
  @rand @UVM_DEFAULT riscv_reg_t       tp;
  @rand @UVM_DEFAULT riscv_reg_t       ra;

  // Options for privileged mode CSR checking
  // Below checking can be made optional as the ISS implementation could be different with the
  // processor.
  bool                    check_misa_init_val = false;
  bool                    check_xstatus = true;

  // Virtual address translation is on for this test
  @rand bool              virtual_addr_translation_on;

  // Vector extension setting
  @rand riscv_vector_cfg  vector_cfg;

  // PMP configuration settings
  @rand riscv_pmp_cfg     pmp_cfg;


  //-----------------------------------------------------------------------------
  //  User space memory region and stack setting
  //-----------------------------------------------------------------------------

  mem_region_t[] mem_region = [{"region_0", 4096, toBit!0b111},
			       {"region_1", 4096*16, toBit!0b111}];

  // Dedicated shared memory region for multi-harts atomic operations
  mem_region_t[] amo_region = [{"amo_0", 64, toBit!0b111}];

  // Stack section word length
  int stack_len = 5000;

  //-----------------------------------------------------------------------------
  // Kernel section setting, used by supervisor mode programs
  //-----------------------------------------------------------------------------

  mem_region_t[] s_mem_region =[{"s_region_0",  4096, toBit!0b111},
				{"s_region_1",  4096, toBit!0b111}];

  // Kernel Stack section word length
  int kernel_stack_len = 4000;

  // Number of instructions for each kernel program
  int kernel_program_instr_cnt = 400;

  // Queue of all the main implemented CSRs that the boot privilege mode cannot access
  // e.g. these CSRs are in higher privilege modes - access should raise an exception
  privileged_reg_t[]       invalid_priv_mode_csrs;

  //-----------------------------------------------------------------------------
  // Command line options or control knobs
  //-----------------------------------------------------------------------------
  // Main options for RISC-V assembly program generation
  // Number of sub-programs per test
  int                    num_of_sub_program = 5;
  int                    instr_cnt = 200;
  int                    num_of_tests = 1;
  // For tests doesn't involve load/store, the data section generation could be skipped
  @UVM_DEFAULT bool                    no_data_page;
  // Options to turn off some specific types of instructions
  @UVM_DEFAULT bool                    no_branch_jump;     // No branch/jump instruction
  @UVM_DEFAULT bool                    no_load_store;      // No load/store instruction
  @UVM_DEFAULT bool                    no_csr_instr;       // No csr instruction
  @UVM_DEFAULT bool                    no_ebreak = true;      // No ebreak instruction
  @UVM_DEFAULT bool                    no_dret = true;        // No dret instruction
  @UVM_DEFAULT bool                    no_fence;           // No fence instruction
  @UVM_DEFAULT bool                    no_wfi = true;         // No WFI instruction
  @UVM_DEFAULT bool                    enable_unaligned_load_store;
  @UVM_DEFAULT int                     illegal_instr_ratio;
  @UVM_DEFAULT int                     hint_instr_ratio;
  // Number of harts to be simulated, must be <= NUM_HARTS
  @UVM_DEFAULT int                     num_of_harts = NUM_HARTS;
  // Use SP as stack pointer
  @UVM_DEFAULT bool                    fix_sp;
  // Use push/pop section for data pages
  @UVM_DEFAULT bool                    use_push_data_section = false;
  // Directed boot privileged mode, u, m, s
  @UVM_DEFAULT string                  boot_mode_opts;
  @UVM_DEFAULT bool                    enable_page_table_exception; // int in SV version
  @UVM_DEFAULT bool                    no_directed_instr;
  // A name suffix for the generated assembly program
  string                  asm_test_suffix;
  // Enable interrupt bit in MSTATUS (MIE, SIE, UIE)
  @UVM_DEFAULT bool                    enable_interrupt;
  bool                    enable_nested_interrupt;
  // We need a separate control knob for enabling timer interrupts, as Spike
  // throws an exception if xIE.xTIE is enabled
  @UVM_DEFAULT bool                    enable_timer_irq;
  // Generate a bare program without any init/exit/error handling/page table routines
  // The generated program can be integrated with a larger program.
  // Note that the bare mode program is not expected to run in standalone mode
  @UVM_DEFAULT bool                    bare_program_mode;
  // Enable accessing illegal CSR instruction
  // - Accessing non-existence CSR
  // - Accessing CSR with wrong privileged mode
  @UVM_DEFAULT bool                    enable_illegal_csr_instruction;
  // Enable accessing CSRs at an invalid privilege level
  @UVM_DEFAULT bool                    enable_access_invalid_csr_level;
  // Enable misaligned instruction (caused by JALR instruction)
  @UVM_DEFAULT bool                    enable_misaligned_instr;
  // Enable some dummy writes to main system CSRs (xSTATUS/xIE) at beginning of test
  // to check repeated writes
  @UVM_DEFAULT bool                    enable_dummy_csr_write;
  @UVM_DEFAULT bool                    randomize_csr = false;
  // sfence support
  @UVM_DEFAULT bool                    allow_sfence_exception = false;
  // Interrupt/Exception Delegation
  @UVM_DEFAULT bool                    no_delegation = true;
  @UVM_DEFAULT bool                    force_m_delegation = false;
  @UVM_DEFAULT bool                    force_s_delegation = false;
  @UVM_DEFAULT bool                    support_supervisor_mode;
  @UVM_DEFAULT bool                    disable_compressed_instr;
  // "Memory mapped" address that when written to will indicate some event to
  // the testbench - testbench will take action based on the value written
  @UVM_DEFAULT ubvec!XLEN              signature_addr = 0xdead_beef;
  @UVM_DEFAULT bool                    require_signature_addr = false;
  // Enable a full or empty debug_rom section.
  // Full debug_rom will contain random instruction streams.
  // Empty debug_rom will contain just dret instruction and will return immediately.
  // Will be empty by default.
  @UVM_DEFAULT bool                    gen_debug_section = false;
  // Enable generation of a directed sequence of instructions containing
  // ebreak inside the debug_rom.
  // Disabled by default.
  @UVM_DEFAULT bool                    enable_ebreak_in_debug_rom = false;
  // Enable setting dcsr.ebreak(m/s/u)
  @UVM_DEFAULT bool                    set_dcsr_ebreak = false;
  // Number of sub programs in the debug rom
  @UVM_DEFAULT int                     num_debug_sub_program = 0;
  // Enable debug single stepping
  @UVM_DEFAULT bool                    enable_debug_single_step = false;
  // Number of single stepping iterations
  @UVM_DEFAULT @rand int               single_step_iterations;
  // Enable mstatus.tw bit - causes u-mode WFI to raise illegal instruction exceptions
  @UVM_DEFAULT bool                    set_mstatus_tw;
  // Enable users to set mstatus.mprv to enable privilege checks on memory accesses.
  @UVM_DEFAULT bool                    set_mstatus_mprv;
  // Stack space allocated to each program, need to be enough to store necessary context
  // Example: RA, SP, T0
  uint                    min_stack_len_per_program = 10 * (XLEN/8);
  uint                    max_stack_len_per_program = 16 * (XLEN/8);
  // Maximum branch distance, avoid skipping large portion of the code
  @UVM_DEFAULT uint                    max_branch_step = 20;
  // Maximum directed instruction stream sequence count
  @UVM_DEFAULT uint                    max_directed_instr_stream_seq = 20;
  // Reserved registers
  @UVM_DEFAULT riscv_reg_t[]           reserved_regs;
  // Floating point support
  @UVM_DEFAULT bool                    enable_floating_point;

  // Vector extension support
  @UVM_DEFAULT bool                    enable_vector_extension;
  // Only generate vector instructions
  @UVM_DEFAULT bool                    vector_instr_only;
  // Bit manipulation extension support
  @UVM_DEFAULT bool                    enable_b_extension;

  @UVM_DEFAULT bool                    enable_zba_extension;
  @UVM_DEFAULT bool                    enable_zbb_extension;
  @UVM_DEFAULT bool                    enable_zbc_extension;
  @UVM_DEFAULT bool                    enable_zbs_extension;

  @UVM_DEFAULT b_ext_group_t[]         enable_bitmanip_groups =
    [b_ext_group_t.ZBB, b_ext_group_t.ZBS, b_ext_group_t.ZBP, b_ext_group_t.ZBE,
     b_ext_group_t.ZBF, b_ext_group_t.ZBC, b_ext_group_t.ZBR, b_ext_group_t.ZBM,
     b_ext_group_t.ZBT, b_ext_group_t.ZB_TMP];

  //-----------------------------------------------------------------------------
  // Command line options for instruction distribution control
  //-----------------------------------------------------------------------------
  int                     dist_control_mode;
  uint[riscv_instr_category_t] category_dist;

  riscv_instr_registry instr_registry;

  CommandLine cmdl;

  constraint! q{
    sub_program_instr_cnt.length == num_of_sub_program;
    debug_sub_program_instr_cnt.length == num_debug_sub_program;
    main_program_instr_cnt inside [10:instr_cnt];
    foreach (cnt; sub_program_instr_cnt) {
      cnt inside [10:instr_cnt];
    }
    // Disable sfence if the program is not boot to supervisor mode
    // If sfence exception is allowed, we can enable sfence instruction in any priviledged mode.
    // When MSTATUS.TVM is set, executing sfence.vma will be treate as illegal instruction

    if (allow_sfence_exception) {
      enable_sfence == true;
      (init_privileged_mode != privileged_mode_t.SUPERVISOR_MODE) || mstatus_tvm == true;
    }
    else {
      (init_privileged_mode != privileged_mode_t.SUPERVISOR_MODE || !support_sfence || mstatus_tvm
       || no_fence) -> (enable_sfence == false);
    }
  } default_c;

  constraint! q{
    if (support_debug_mode) {
      debug_program_instr_cnt inside [100:300];
      foreach (cnt; debug_sub_program_instr_cnt) {
	cnt inside [100:300];
      }
    }
    main_program_instr_cnt + sub_program_instr_cnt.sum == instr_cnt;
  } debug_mode_c;

  // Keep the number of single step iterations relatively small
  constraint! q{
    if (enable_debug_single_step) {
      single_step_iterations inside [10 : 50];
    }
  } debug_single_step_c;

  // Boot privileged mode distribution
   constraint! q{
     // Boot to higher privileged mode more often
     if (supported_privileged_mode.length == 2) {
       init_privileged_mode dist [supported_privileged_mode[0] := 6,
                                  supported_privileged_mode[1] := 4];
     }
     else if (supported_privileged_mode.length == 3) {
       init_privileged_mode dist [supported_privileged_mode[0] := 4,
				  supported_privileged_mode[1] := 3,
                                  supported_privileged_mode[2] := 3];
     }
     else {
       init_privileged_mode == supported_privileged_mode[0];
     }
   } boot_privileged_mode_dist_c;

  immutable int tvec_align =  clog2((XLEN*4)/8);

  constraint! q{
      mtvec_mode inside [supported_interrupt_mode];
    if (mtvec_mode == mtvec_mode_t.DIRECT) {
      @soft tvec_alignment == 2;
    } else {
      // Setting MODE = Vectored may impose an additional alignmentconstraint on BASE,
      // requiring up to 4×XLEN-byte alignment
      @soft tvec_alignment == tvec_align;
    }
  } mtvec_c;


  constraint! q{
    // This is default disabled at setup phase. It can be enabled in the exception and interrupt
    // handling routine
    if (set_mstatus_mprv == true) {
      mstatus_mprv == true;
    } else {
      mstatus_mprv == false;
    }
    if (SATP_MODE == satp_mode_t.BARE) {
      mstatus_mxr == false;
      mstatus_sum == false;
      mstatus_tvm == false;
    }
  } mstatus_c;

  // Exception delegation setting
  constraint! q{
    // Do not delegate instructino page fault to supervisor/user mode because this may introduce
    // dead loop. All the subsequent instruction fetches may fail and program cannot recover.
    m_mode_exception_delegation[exception_cause_t.INSTRUCTION_PAGE_FAULT] == false;
    if (force_m_delegation) {
      foreach (del, enbl; m_mode_exception_delegation) {
	@soft enbl == true;
      }
      foreach (del, enbl; m_mode_interrupt_delegation) {
	@soft enbl == true;
      }
    }
    if (force_s_delegation) {
      foreach (del, enbl; s_mode_exception_delegation) {
	@soft enbl == true;
      }
      foreach (del, enbl; s_mode_interrupt_delegation) {
	@soft enbl == true;
      }
    }
  } exception_delegation_c;

  // Spike only supports a subset of exception and interrupt delegation
  // You can modify this constraint if your ISS support different set of delegations
  constraint! q{
    foreach (del, enbl; m_mode_exception_delegation) {
       if (!support_supervisor_mode || no_delegation) {
         enbl == false;
       }
       if (del !inside [exception_cause_t.INSTRUCTION_ADDRESS_MISALIGNED,
			exception_cause_t.BREAKPOINT,
			exception_cause_t.ECALL_UMODE,
			exception_cause_t.INSTRUCTION_PAGE_FAULT,
			exception_cause_t.LOAD_PAGE_FAULT,
			exception_cause_t.STORE_AMO_PAGE_FAULT]) {
         enbl == false;
       }
     }
    foreach (del, enbl; m_mode_interrupt_delegation) {
       if (!support_supervisor_mode || no_delegation) {
         enbl == false;
       }
       if (del !inside [interrupt_cause_t.S_SOFTWARE_INTR,
			interrupt_cause_t.S_TIMER_INTR,
			interrupt_cause_t.S_EXTERNAL_INTR]) {
         enbl == false;
       }
     }
  } delegation_c;

  constraint! q{
    ra dist [riscv_reg_t.RA := 3, riscv_reg_t.T1 := 2,
	     riscv_reg_t.SP:riscv_reg_t.T0 :/ 1,
	     riscv_reg_t.T2:riscv_reg_t.T6 :/ 4];
    ra != sp;
    ra != tp;
    ra != riscv_reg_t.ZERO;
  } ra_c;

  constraint! q{
    if (fix_sp) {
      sp == riscv_reg_t.SP;
    }
    sp != tp;
    sp !inside [riscv_reg_t.GP, riscv_reg_t.RA, riscv_reg_t.ZERO];
    tp !inside [riscv_reg_t.GP, riscv_reg_t.RA, riscv_reg_t.ZERO];
  }  sp_tp_c;

  constraint! q{
    scratch_reg !inside [riscv_reg_t.ZERO, sp, tp, ra, riscv_reg_t.GP];
  } reserve_scratch_reg_c;

  // This reg is only used inside PMP exception routine,
  // so we can be a bit looser with constraints.
  constraint! q{
    pmp_reg !inside [riscv_reg_t.ZERO, sp, tp];
  } reserve_pmp_reg_c;


  constraint! q{
    foreach (r; gpr) {
      r !inside [sp, tp, scratch_reg, pmp_reg, riscv_reg_t.ZERO,
		 riscv_reg_t.RA, riscv_reg_t.GP];
    }
    unique [gpr];
  } gpr_c;

   constraint! q{
     solve init_privileged_mode before virtual_addr_translation_on;
   } addr_translation_rnd_order_c;

  constraint! q{
    if ((init_privileged_mode != privileged_mode_t.MACHINE_MODE) &&
	(SATP_MODE != satp_mode_t.BARE)) {
      virtual_addr_translation_on == true;
    }
    else {
      virtual_addr_translation_on == false;
    }
  } addr_translation_c;


  constraint! q{
    if (enable_floating_point) {
      mstatus_fs == 1;
    }
    else {
      mstatus_fs == 0;
    }
  } floating_point_c;


  constraint! q{
    if (enable_vector_extension) {
      mstatus_vs == 1;
    }
    else {
      mstatus_vs == 0;
    }
  } mstatus_vs_c;

  // `uvm_object_utils_begin(riscv_instr_gen_config)
  //   `uvm_field_int(main_program_instr_cnt, UVM_DEFAULT)
  //   `uvm_field_sarray_int(sub_program_instr_cnt, UVM_DEFAULT)
  //   `uvm_field_int(debug_program_instr_cnt, UVM_DEFAULT)
  //   `uvm_field_enum(data_pattern_t, data_page_pattern, UVM_DEFAULT)
  //   `uvm_field_enum(privileged_mode_t, init_privileged_mode, UVM_DEFAULT)
  //   `uvm_field_array_enum(riscv_reg_t, reserved_regs, UVM_DEFAULT)
  //   `uvm_field_enum(riscv_reg_t, ra, UVM_DEFAULT)
  //   `uvm_field_enum(riscv_reg_t, sp, UVM_DEFAULT)
  //   `uvm_field_enum(riscv_reg_t, tp, UVM_DEFAULT)
  //   `uvm_field_int(tvec_alignment, UVM_DEFAULT)
  //   `uvm_field_int(no_data_page, UVM_DEFAULT)
  //   `uvm_field_int(no_branch_jump, UVM_DEFAULT)
  //   `uvm_field_int(no_load_store, UVM_DEFAULT)
  //   `uvm_field_int(no_csr_instr, UVM_DEFAULT)
  //   `uvm_field_int(no_ebreak, UVM_DEFAULT)
  //   `uvm_field_int(no_dret, UVM_DEFAULT)
  //   `uvm_field_int(no_fence, UVM_DEFAULT)
  //   `uvm_field_int(no_wfi, UVM_DEFAULT)
  //   `uvm_field_int(fix_sp, UVM_DEFAULT)
  //   `uvm_field_int(enable_unaligned_load_store, UVM_DEFAULT)
  //   `uvm_field_int(illegal_instr_ratio, UVM_DEFAULT)
  //   `uvm_field_int(hint_instr_ratio, UVM_DEFAULT)
  //   `uvm_field_string(boot_mode_opts, UVM_DEFAULT)
  //   `uvm_field_int(enable_page_table_exception, UVM_DEFAULT)
  //   `uvm_field_int(no_directed_instr, UVM_DEFAULT)
  //   `uvm_field_int(enable_interrupt, UVM_DEFAULT)
  //   `uvm_field_int(enable_timer_irq, UVM_DEFAULT)
  //   `uvm_field_int(bare_program_mode, UVM_DEFAULT)
  //   `uvm_field_int(enable_illegal_csr_instruction, UVM_DEFAULT)
  //   `uvm_field_int(enable_access_invalid_csr_level, UVM_DEFAULT)
  //   `uvm_field_int(enable_misaligned_instr, UVM_DEFAULT)
  //   `uvm_field_int(enable_dummy_csr_write, UVM_DEFAULT)
  //   `uvm_field_int(randomize_csr, UVM_DEFAULT)
  //   `uvm_field_int(allow_sfence_exception, UVM_DEFAULT)
  //   `uvm_field_int(no_delegation, UVM_DEFAULT)
  //   `uvm_field_int(force_m_delegation, UVM_DEFAULT)
  //   `uvm_field_int(force_s_delegation, UVM_DEFAULT)
  //   `uvm_field_int(support_supervisor_mode, UVM_DEFAULT)
  //   `uvm_field_int(disable_compressed_instr, UVM_DEFAULT)
  //   `uvm_field_int(signature_addr, UVM_DEFAULT)
  //   `uvm_field_int(num_of_harts, UVM_DEFAULT)
  //   `uvm_field_int(require_signature_addr, UVM_DEFAULT)
  //   `uvm_field_int(gen_debug_section, UVM_DEFAULT)
  //   `uvm_field_int(enable_ebreak_in_debug_rom, UVM_DEFAULT)
  //   `uvm_field_int(set_dcsr_ebreak, UVM_DEFAULT)
  //   `uvm_field_int(num_debug_sub_program, UVM_DEFAULT)
  //   `uvm_field_int(enable_debug_single_step, UVM_DEFAULT)
  //   `uvm_field_int(single_step_iterations, UVM_DEFAULT)
  //   `uvm_field_int(set_mstatus_tw, UVM_DEFAULT)
  //   `uvm_field_int(set_mstatus_mprv, UVM_DEFAULT)
  //   `uvm_field_int(max_branch_step, UVM_DEFAULT)
  //   `uvm_field_int(max_directed_instr_stream_seq, UVM_DEFAULT)
  //   `uvm_field_int(enable_floating_point, UVM_DEFAULT)
  //   `uvm_field_int(enable_vector_extension, UVM_DEFAULT)
  //   `uvm_field_int(vector_instr_only, UVM_DEFAULT)
  //   `uvm_field_int(enable_b_extension, UVM_DEFAULT)
  //   `uvm_field_array_enum(b_ext_group_t, enable_bitmanip_groups, UVM_DEFAULT)
  //   `uvm_field_int(use_push_data_section, UVM_DEFAULT)
  // `uvm_object_utils_end



  this(string name = "") {
    // string s;
    instr_registry = riscv_instr_registry.type_id.create("registry");
    register_isa(instr_registry);
    instr_registry.set_cfg(this);
    riscv_instr_group_t[] march_isa;
    super(name);
    init_delegation();
    // inst = uvm_cmdline_processor::get_inst(); // call uvm_cmdline_proc() directly instead
    cmdl = new CommandLine();
    get_int_arg_value("+num_of_tests=", num_of_tests);
    get_bool_arg_value("+enable_page_table_exception=", enable_page_table_exception);
    get_bool_arg_value("+enable_interrupt=", enable_interrupt);
    get_bool_arg_value("+enable_nested_interrupt=", enable_nested_interrupt);
    get_bool_arg_value("+enable_timer_irq=", enable_timer_irq);
    get_int_arg_value("+num_of_sub_program=", num_of_sub_program);
    get_int_arg_value("+instr_cnt=", instr_cnt);
    get_bool_arg_value("+no_ebreak=", no_ebreak);
    get_bool_arg_value("+no_dret=", no_dret);
    get_bool_arg_value("+no_wfi=", no_wfi);
    get_bool_arg_value("+no_branch_jump=", no_branch_jump);
    get_bool_arg_value("+no_load_store=", no_load_store);
    get_bool_arg_value("+no_csr_instr=", no_csr_instr);
    get_bool_arg_value("+fix_sp=", fix_sp);
    get_bool_arg_value("+use_push_data_section=", use_push_data_section);
    get_bool_arg_value("+enable_illegal_csr_instruction=", enable_illegal_csr_instruction);
    get_bool_arg_value("+enable_access_invalid_csr_level=", enable_access_invalid_csr_level);
    get_bool_arg_value("+enable_misaligned_instr=", enable_misaligned_instr);
    get_bool_arg_value("+enable_dummy_csr_write=", enable_dummy_csr_write);
    get_bool_arg_value("+allow_sfence_exception=", allow_sfence_exception);
    get_bool_arg_value("+no_data_page=", no_data_page);
    get_bool_arg_value("+no_directed_instr=", no_directed_instr);
    get_bool_arg_value("+no_fence=", no_fence);
    get_bool_arg_value("+no_delegation=", no_delegation);
    get_int_arg_value("+illegal_instr_ratio=", illegal_instr_ratio);
    get_int_arg_value("+hint_instr_ratio=", hint_instr_ratio);
    get_int_arg_value("+num_of_harts=", num_of_harts);
    get_bool_arg_value("+enable_unaligned_load_store=", enable_unaligned_load_store);
    get_bool_arg_value("+force_m_delegation=", force_m_delegation);
    get_bool_arg_value("+force_s_delegation=", force_s_delegation);
    get_bool_arg_value("+require_signature_addr=", require_signature_addr);
    get_bool_arg_value("+disable_compressed_instr=", disable_compressed_instr);
    get_bool_arg_value("+randomize_csr=", randomize_csr);
    if (require_signature_addr) {
      int signature_addr_int;
      get_hex_arg_value("+signature_addr=", signature_addr_int);
      signature_addr = toubvec!XLEN(signature_addr_int);
    }
    if (cmdl.plusArgs("tvec_alignment=%d", tvec_alignment)) {
      rand_mode!q{tvec_alignment}(false);
    }
    get_bool_arg_value("+gen_debug_section=", gen_debug_section);
    get_bool_arg_value("+bare_program_mode=", bare_program_mode);
    get_int_arg_value("+num_debug_sub_program=", num_debug_sub_program);
    get_bool_arg_value("+enable_ebreak_in_debug_rom=", enable_ebreak_in_debug_rom);
    get_bool_arg_value("+set_dcsr_ebreak=", set_dcsr_ebreak);
    get_bool_arg_value("+enable_debug_single_step=", enable_debug_single_step);
    get_bool_arg_value("+set_mstatus_tw=", set_mstatus_tw);
    get_bool_arg_value("+set_mstatus_mprv=", set_mstatus_mprv);
    get_bool_arg_value("+enable_floating_point=", enable_floating_point);
    get_bool_arg_value("+enable_vector_extension=", enable_vector_extension);
    get_bool_arg_value("+enable_b_extension=", enable_b_extension);
    get_bool_arg_value("+enable_zba_extension=", enable_zba_extension);
    get_bool_arg_value("+enable_zbb_extension=", enable_zbb_extension);
    get_bool_arg_value("+enable_zbc_extension=", enable_zbc_extension);
    get_bool_arg_value("+enable_zbs_extension=", enable_zbs_extension);
    cmdline_enum_processor!(b_ext_group_t).get_array_values("+enable_bitmanip_groups=",
							    enable_bitmanip_groups);
    if (uvm_cmdline_processor.get_inst().get_arg_value("+boot_mode=", boot_mode_opts)) {
      uvm_info(get_full_name(), format("Got boot mode option - %0s", boot_mode_opts), UVM_LOW);
      switch(boot_mode_opts) {
      case  "m": init_privileged_mode = privileged_mode_t.MACHINE_MODE;
	break;
      case "s": init_privileged_mode = privileged_mode_t.SUPERVISOR_MODE;
	break;
      case "u": init_privileged_mode = privileged_mode_t.USER_MODE;
	break;
      default: uvm_fatal(get_full_name(),
			 format("Illegal boot mode option - %0s", boot_mode_opts));
	break;
      }
      rand_mode!q{init_privileged_mode}(false); //
      addr_translation_rnd_order_c.constraint_mode(false);
    }
    uvm_info(get_full_name(), format("riscv_instr_pkg.supported_privileged_mode = %0d",
				     supported_privileged_mode.length), UVM_LOW);
    uvm_cmdline_processor.get_inst().get_arg_value("+asm_test_suffix=", asm_test_suffix);
    // Directed march list from the runtime options, ex. RV32I, RV32M etc.
    cmdline_enum_processor !(riscv_instr_group_t).get_array_values("+march=", march_isa);
    if (march_isa.length != 0) supported_isa = march_isa;

    if (!(canFind(supported_isa, riscv_instr_group_t.RV32C))) {
      disable_compressed_instr = true;
    }

    if (! (supported_isa.canFind(riscv_instr_group_t.RV32ZBA) ||
	   supported_isa.canFind(riscv_instr_group_t.RV64ZBA))) {
      enable_zba_extension = false;
    }

    if (! (supported_isa.canFind(riscv_instr_group_t.RV32ZBB) ||
	   supported_isa.canFind(riscv_instr_group_t.RV64ZBB))) {
      enable_zbb_extension = false;
    }

    if (! (supported_isa.canFind(riscv_instr_group_t.RV32ZBC) ||
	   supported_isa.canFind(riscv_instr_group_t.RV64ZBC))) {
      enable_zbc_extension = false;
    }

    if (! (supported_isa.canFind(riscv_instr_group_t.RV32ZBS) ||
	   supported_isa.canFind(riscv_instr_group_t.RV64ZBS))) {
      enable_zbs_extension = false;
    }

    vector_cfg = riscv_vector_cfg.type_id.create("vector_cfg");
    pmp_cfg = riscv_pmp_cfg.type_id.create("pmp_cfg");
    rand_mode!q{pmp_cfg}(pmp_cfg.pmp_randomize);
    pmp_cfg.initialize(require_signature_addr);
    setup_instr_distribution();
    get_invalid_priv_lvl_csr();
  }

  void setup_instr_distribution() {
    int val;
    get_int_arg_value("+dist_control_mode=", dist_control_mode);
    if (dist_control_mode == 1) {
      foreach (category; [EnumMembers!riscv_instr_category_t]) {
	string opts = format("dist_%0s=", category) ~ "%d";
	opts = opts.toLower();
	if (cmdl.plusArgs(opts, val)) { // $value$plusargs(opts, val)
	  category_dist[category] = val;
	}
	else {
	  category_dist[category] = 10; // Default ratio
	}
	uvm_info(get_full_name(), format("Set dist[%0s] = %0d",
					 category, category_dist[category]), UVM_LOW);
      }
    }
  }

  // Initialize the exception/interrupt delegation associate array, set all delegation default to 0
  void init_delegation() {
    foreach (cause; [EnumMembers!exception_cause_t]) {
      m_mode_exception_delegation[cause] = false;
      s_mode_exception_delegation[cause] = false;
    }
    foreach (cause; [EnumMembers!interrupt_cause_t]) {
      m_mode_interrupt_delegation[cause] = false;
      s_mode_interrupt_delegation[cause] = false;
    }
  }

  void pre_randomize() {
    foreach (mode; supported_privileged_mode) {
      if (mode  == privileged_mode_t.SUPERVISOR_MODE) {
	support_supervisor_mode = true;
      }
    }
  }

  void get_non_reserved_gpr() { }

  void post_randomize() {
    // Setup the list all reserved registers
    reserved_regs = [tp, sp, scratch_reg];
    // Need to save all loop registers, and RA/T0
    min_stack_len_per_program = 2 * (XLEN/8);
    // Check if the setting is legal
    check_setting();
    // WFI is not supported in umode
    if (init_privileged_mode == privileged_mode_t.USER_MODE) {
      no_wfi = true;
    }
    instr_registry.create_instr_list(this);
  }

  void check_setting() {
    bool support_64b = false;
    bool support_128b = false;
    foreach (isa; supported_isa) {
      if (canFind([riscv_instr_group_t.RV64I,
		   riscv_instr_group_t.RV64M,
		   riscv_instr_group_t.RV64A,
		   riscv_instr_group_t.RV64F,
		   riscv_instr_group_t.RV64D,
		   riscv_instr_group_t.RV64C,
		   riscv_instr_group_t.RV64B], isa)) {
	support_64b = true;
      }
      else if (canFind([riscv_instr_group_t.RV128I,
			riscv_instr_group_t.RV128C], isa)) {
	support_128b = true;
      }
    }
    if (support_128b && XLEN != 128) {
      uvm_fatal(get_full_name(),
		"XLEN should be set to 128 based on riscv_instr_pkg.supported_isa setting");
    }
    if (!support_128b && support_64b && XLEN != 64) {
      uvm_fatal(get_full_name(),
		"XLEN should be set to 64 based on riscv_instr_pkg.supported_isa setting");
    }
    if (!(support_128b || support_64b) && XLEN != 32) {
      uvm_fatal(get_full_name(),
		"XLEN should be set to 32 based on riscv_instr_pkg.supported_isa setting");
    }
    if (!(support_128b || support_64b) &&
	!(canFind([satp_mode_t.SV32,
		   satp_mode_t.BARE], SATP_MODE))) {
      uvm_fatal(get_full_name(),
		format("SATP mode %0s is not supported for RV32G ISA", SATP_MODE));
    }
  }

  // Populate invalid_priv_mode_csrs with the main implemented CSRs for each supported privilege
  // mode
  // TODO(udi) - include performance/pmp/trigger CSRs?
  void get_invalid_priv_lvl_csr() {
    char[] invalid_lvl;
    // Debug CSRs are inaccessible from all but Debug Mode, and we cannot boot into Debug Mode
    invalid_lvl ~= 'D';
    switch (init_privileged_mode) {
    case privileged_mode_t.MACHINE_MODE:
      break;
    case privileged_mode_t.SUPERVISOR_MODE:
      invalid_lvl ~= 'M';
      break;
    case privileged_mode_t.USER_MODE:
      invalid_lvl ~= 'S';
      invalid_lvl ~= 'M';
      break;
    default:
      uvm_fatal(get_full_name(), "Unsupported initialization privilege mode");
      break;
    }
    foreach (csr; implemented_csr) {
      string csr_name = csr.to!string();
      if (canFind(invalid_lvl, csr)) {
	  invalid_priv_mode_csrs ~= csr;
      }
    }
  }
}
