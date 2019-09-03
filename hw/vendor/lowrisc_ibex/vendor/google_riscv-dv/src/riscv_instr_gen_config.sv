/*
 * Copyright 2018 Google LLC
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

class riscv_instr_gen_config extends uvm_object;

  //-----------------------------------------------------------------------------
  // Random instruction generation settings
  //-----------------------------------------------------------------------------

  // Instruction count of the main program
  rand int               main_program_instr_cnt;

  // Instruction count of each sub-program
  rand int               sub_program_instr_cnt[];

  // Instruction count of the debug rom
  rand int               debug_program_instr_cnt;

  // Instruction count of debug sub-programs
  rand int               debug_sub_program_instr_cnt[];

  // Pattern of data section: RAND_DATA, ALL_ZERO, INCR_VAL
  rand data_pattern_t    data_page_pattern;

  // Max depth for the nested loops
  rand bit [1:0]         max_nested_loop;

  // Associate array for delegation configuration for each exception and interrupt
  // When the bit is 1, the corresponding delegation is enabled.
  rand bit               m_mode_exception_delegation[exception_cause_t];
  rand bit               s_mode_exception_delegation[exception_cause_t];
  rand bit               m_mode_interrupt_delegation[interrupt_cause_t];
  rand bit               s_mode_interrupt_delegation[interrupt_cause_t];

  // Priviledged mode after boot
  rand privileged_mode_t init_privileged_mode;

  // Key fields in xSTATUS
  // Memory protection bits
  rand bit               mstatus_mprv;
  rand bit               mstatus_mxr;
  rand bit               mstatus_sum;
  rand bit               mstatus_tvm;
  rand mtvec_mode_t      mtvec_mode;

  // Enable sfence.vma instruction
  rand bit               enable_sfence;

  // Options for privileged mode CSR checking
  // Below checking can be made optional as the ISS implementation could be different with the
  // processor.
  bit                    check_misa_init_val = 1'b0;
  bit                    check_xstatus = 1'b1;

  //-----------------------------------------------------------------------------
  // Instruction list based on the config, generate by build_instruction_template
  //-----------------------------------------------------------------------------
  riscv_instr_base       instr_template[riscv_instr_name_t];
  riscv_instr_name_t     basic_instr[$];
  riscv_instr_name_t     instr_group[riscv_instr_cateogry_t][$];
  riscv_instr_name_t     instr_category[riscv_instr_cateogry_t][$];

  //-----------------------------------------------------------------------------
  // Command line options or control knobs
  //-----------------------------------------------------------------------------
  // Main options for RISC-V assembly program generation
  // Number of sub-programs per test
  int                    num_of_sub_program = 5;
  int                    instr_cnt = 200;
  int                    num_of_tests = 1;
  // For tests doesn't involve load/store, the data section generation could be skipped
  bit                    no_data_page;
  // Options to turn off some specific types of instructions
  bit                    no_branch_jump;   // No branch/jump instruction
  bit                    no_load_store;    // No load/store instruction
  bit                    no_csr_instr;     // No csr instruction
  bit                    no_ebreak = 1;    // No ebreak instruction
  bit                    no_fence;         // No fence instruction
  bit                    no_wfi = 1;       // No WFI instruction
  bit                    enable_unaligned_load_store;
  bit                    enable_illegal_instruction;
  bit                    enable_hint_instruction;
  int                    bin_program_instr_cnt = 200;
  // Directed boot privileged mode, u, m, s
  string                 boot_mode_opts;
  int                    enable_page_table_exception;
  bit                    no_directed_instr;
  // A name suffix for the generated assembly program
  string                 asm_test_suffix;
  // Enable interrupt bit in MSTATUS (MIE, SIE, UIE)
  int                    enable_interrupt;
  // Enable accessing illegal CSR instruction
  // - Accessing non-existence CSR
  // - Accessing CSR with wrong privileged mode
  bit                    enable_illegal_csr_instruction;
  // sfence support
  bit                    allow_sfence_exception = 0;
  // Interrupt/Exception Delegation
  bit                    no_delegation = 1;
  bit                    force_m_delegation = 0;
  bit                    force_s_delegation = 0;
  bit                    support_supervisor_mode;
  // "Memory mapped" address that when written to will indicate some event to
  // the testbench - testbench will take action based on the value written
  int                    signature_addr = 32'hdead_beef;
  bit                    require_signature_addr = 1'b0;
  rand riscv_reg_t       signature_addr_reg;
  rand riscv_reg_t       signature_data_reg;
  bit                    gen_debug_section = 1'b0;
  // Enable a full or empty debug_rom section.
  // Full debug_rom will contain random instruction streams.
  // Empty debug_rom will contain just dret instruction and will return immediately.
  // Will be empty by default.
  bit                    empty_debug_section = 1'b0;
  // Number of sub programs in the debug rom
  int                    num_debug_sub_program = 0;
  // Stack space allocated to each program, need to be enough to store necessary context
  // Example: RA, SP, T0, loop registers
  int                    min_stack_len_per_program = 10 * (XLEN/8);
  int                    max_stack_len_per_program = 16 * (XLEN/8);
  // Maximum branch distance, avoid skipping large portion of the code
  int                    max_branch_step = 20;
  // Maximum directed instruction stream sequence count
  int                    max_directed_instr_stream_seq = 20;
  // Reserved registers
  // Default reserved registers, only used by special instructions
  riscv_reg_t            default_reserved_regs[];
  // Reserve some registers for loop counter, make sure the loop can execute
  // in a determinstic way and not affected by other random instructions
  rand riscv_reg_t       loop_regs[];
  // All reserved regs
  riscv_reg_t            reserved_regs[];

  uvm_cmdline_processor  inst;

  constraint default_c {
    sub_program_instr_cnt.size() == num_of_sub_program;
    debug_sub_program_instr_cnt.size() == num_debug_sub_program;
    if (riscv_instr_pkg::support_debug_mode) {
      main_program_instr_cnt + sub_program_instr_cnt.sum()
                             + debug_program_instr_cnt
                             + debug_sub_program_instr_cnt.sum() == instr_cnt;
      debug_program_instr_cnt inside {[100 : 300]};
      foreach(debug_sub_program_instr_cnt[i]) {
        debug_sub_program_instr_cnt[i] inside {[100 : 300]};
      }
    } else {
      main_program_instr_cnt + sub_program_instr_cnt.sum() == instr_cnt;
    }
    main_program_instr_cnt inside {[10 : instr_cnt]};
    foreach(sub_program_instr_cnt[i]) {
      sub_program_instr_cnt[i] inside {[10 : instr_cnt]};
    }
    // Disable sfence if the program is not boot to supervisor mode
    // If sfence exception is allowed, we can enable sfence instruction in any priviledged mode.
    // When MSTATUS.TVM is set, executing sfence.vma will be treate as illegal instruction
    if(allow_sfence_exception) {
      enable_sfence == 1'b1;
      (init_privileged_mode != SUPERVISOR_MODE) || (mstatus_tvm == 1'b1);
    } else {
      (init_privileged_mode != SUPERVISOR_MODE || !riscv_instr_pkg::support_sfence || mstatus_tvm || no_fence)
                                                     -> (enable_sfence == 1'b0);
    }
  }

  // Boot privileged mode distribution
  constraint boot_privileged_mode_dist_c {
    // Boot to higher privileged mode more often
    if(riscv_instr_pkg::supported_privileged_mode.size() == 2) {
      init_privileged_mode dist {riscv_instr_pkg::supported_privileged_mode[0] := 9,
                                 riscv_instr_pkg::supported_privileged_mode[1] := 1};
    } else if (riscv_instr_pkg::supported_privileged_mode.size() == 3) {
      init_privileged_mode dist {riscv_instr_pkg::supported_privileged_mode[0] := 6,
                                 riscv_instr_pkg::supported_privileged_mode[1] := 3,
                                 riscv_instr_pkg::supported_privileged_mode[2] := 1};
    } else {
      init_privileged_mode == riscv_instr_pkg::supported_privileged_mode[0];
    }
  }

  constraint mtvec_c {
    mtvec_mode inside {supported_interrupt_mode};
  }

  constraint mstatus_c {
    // This is default disabled at setup phase. It can be enabled in the exception and interrupt
    // handling routine
    mstatus_mprv == 1'b0;
  }

  // Exception delegation setting
  constraint exception_delegation_c {
    // Do not delegate instructino page fault to supervisor/user mode because this may introduce
    // dead loop. All the subsequent instruction fetches may fail and program cannot recover.
    m_mode_exception_delegation[INSTRUCTION_PAGE_FAULT] == 1'b0;
    if(force_m_delegation) {
      foreach(m_mode_exception_delegation[i]) {
        soft m_mode_exception_delegation[i] == 1'b1;
      }
      foreach(m_mode_interrupt_delegation[i]) {
        soft m_mode_interrupt_delegation[i] == 1'b1;
      }
    }
    if(force_s_delegation) {
      foreach(s_mode_exception_delegation[i]) {
        soft s_mode_exception_delegation[i] == 1'b1;
      }
      foreach(s_mode_interrupt_delegation[i]) {
        soft s_mode_interrupt_delegation[i] == 1'b1;
      }
    }
  }

  // Spike only supports a subset of exception and interrupt delegation
  // You can modify this constraint if your ISS support different set of delegations
  constraint delegation_c {
    foreach(m_mode_exception_delegation[i]) {
      if(!support_supervisor_mode) {
        m_mode_exception_delegation[i] == 0;
      }
      if(!(i inside {INSTRUCTION_ADDRESS_MISALIGNED, BREAKPOINT, ECALL_UMODE,
                     INSTRUCTION_PAGE_FAULT, LOAD_PAGE_FAULT, STORE_AMO_PAGE_FAULT})) {
        m_mode_exception_delegation[i] == 0;
      }
    }
    foreach(m_mode_interrupt_delegation[i]) {
      if(!support_supervisor_mode) {
        m_mode_interrupt_delegation[i] == 0;
      }
      if(!(i inside {S_SOFTWARE_INTR, S_TIMER_INTR, S_EXTERNAL_INTR})) {
        m_mode_interrupt_delegation[i] == 0;
      }
    }
  }

  constraint reserved_reg_c {
    unique {loop_regs};
    foreach(loop_regs[i]) {
      !(loop_regs[i] inside {default_reserved_regs});
    }
    !(signature_addr_reg inside {ZERO, default_reserved_regs, loop_regs});
    !(signature_data_reg inside {ZERO, default_reserved_regs, loop_regs});
    signature_addr_reg != signature_data_reg;
  }

  constraint legal_loop_regs_c {
    soft max_nested_loop != 0;
    // One register for loop counter, one for loop limit
    loop_regs.size() == max_nested_loop*2;
    unique {loop_regs};
    foreach(loop_regs[i]) {
      loop_regs[i] != ZERO;
    }
  }

  `uvm_object_utils_begin(riscv_instr_gen_config)
    `uvm_field_int(main_program_instr_cnt,       UVM_DEFAULT)
    `uvm_field_sarray_int(sub_program_instr_cnt, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    string s;
    super.new(name);
    setup_default_reserved_regs();
    init_delegation();
    inst = uvm_cmdline_processor::get_inst();
    get_int_arg_value("+num_of_tests=", num_of_tests);
    get_int_arg_value("+enable_page_table_exception=", enable_page_table_exception);
    get_int_arg_value("+enable_interrupt=", enable_interrupt);
    get_int_arg_value("+num_of_sub_program=", num_of_sub_program);
    get_int_arg_value("+instr_cnt=", instr_cnt);
    get_bool_arg_value("+no_ebreak=", no_ebreak);
    get_bool_arg_value("+no_wfi=", no_wfi);
    get_bool_arg_value("+no_branch_jump=", no_branch_jump);
    get_bool_arg_value("+no_load_store=", no_load_store);
    get_bool_arg_value("+no_csr_instr=", no_csr_instr);
    get_bool_arg_value("+enable_illegal_csr_instruction=", enable_illegal_csr_instruction);
    get_bool_arg_value("+allow_sfence_exception=", allow_sfence_exception);
    get_bool_arg_value("+no_data_page=", no_data_page);
    get_bool_arg_value("+no_directed_instr=", no_directed_instr);
    get_bool_arg_value("+no_fence=", no_fence);
    get_bool_arg_value("+no_delegation=", no_delegation);
    get_bool_arg_value("+enable_unaligned_load_store=", enable_unaligned_load_store);
    get_bool_arg_value("+enable_illegal_instruction=", enable_illegal_instruction);
    get_bool_arg_value("+enable_hint_instruction=", enable_hint_instruction);
    get_bool_arg_value("+force_m_delegation=", force_m_delegation);
    get_bool_arg_value("+force_s_delegation=", force_s_delegation);
    get_bool_arg_value("+require_signature_addr=", require_signature_addr);
    if (this.require_signature_addr) begin
      get_hex_arg_value("+signature_addr=", signature_addr);
    end
    get_bool_arg_value("+gen_debug_section=", gen_debug_section);
    get_int_arg_value("+num_debug_sub_program=", num_debug_sub_program);
    if(inst.get_arg_value("+boot_mode=", boot_mode_opts)) begin
      `uvm_info(get_full_name(), $sformatf(
                "Got boot mode option - %0s", boot_mode_opts), UVM_LOW)
      case(boot_mode_opts)
        "m" : init_privileged_mode = MACHINE_MODE;
        "s" : init_privileged_mode = SUPERVISOR_MODE;
        "u" : init_privileged_mode = USER_MODE;
        default: `uvm_fatal(get_full_name(),
                  $sformatf("Illegal boot mode option - %0s", boot_mode_opts))
      endcase
      init_privileged_mode.rand_mode(0);
    end
    `uvm_info(`gfn, $sformatf("riscv_instr_pkg::supported_privileged_mode = %0d",
                   riscv_instr_pkg::supported_privileged_mode.size()), UVM_LOW)
    void'(inst.get_arg_value("+asm_test_suffix=", asm_test_suffix));
    // Directed march list from the runtime options, ex. RV32I, RV32M etc.
    void'(inst.get_arg_value("+march=", s));
    if(s != "") begin
      string cmdline_march_list[$];
      riscv_instr_group_t march;
      uvm_split_string(s, ",", cmdline_march_list);
      riscv_instr_pkg::supported_isa.delete();
      foreach(cmdline_march_list[i]) begin
        if(uvm_enum_wrapper#(riscv_instr_group_t)::from_name(
           cmdline_march_list[i].toupper(), march)) begin
          riscv_instr_pkg::supported_isa.push_back(march);
        end else begin
          `uvm_fatal(get_full_name(), $sformatf(
                     "Invalid march %0s specified in command line", cmdline_march_list[i]))
        end
      end
    end
  endfunction

  // Initialize the exception/interrupt delegation associate array, set all delegation default to 0
  virtual function void init_delegation();
    exception_cause_t cause;
    interrupt_cause_t intr_cause;
    cause = cause.first;
    // Init exception delegation array
    do begin
      m_mode_exception_delegation[cause] = 1'b0;
      s_mode_exception_delegation[cause] = 1'b0;
      cause = cause.next;
    end
    while(cause != cause.first);
    // Init interrupt delegation array
    intr_cause = intr_cause.first;
    do begin
      m_mode_interrupt_delegation[intr_cause] = 1'b0;
      s_mode_interrupt_delegation[intr_cause] = 1'b0;
      intr_cause = intr_cause.next;
    end
    while(intr_cause != intr_cause.first);
  endfunction

  // Reserve below registers for special purpose instruction
  // The other normal instruction cannot use them as destination register
  virtual function void setup_default_reserved_regs();
    default_reserved_regs = {RA, // x1, return address
                             SP, // x2, stack pointer (user stack)
                             TP, // x4, thread pointer, used as kernel stack pointer
                             T0  // x5, alternative link pointer
                             };
  endfunction

  function void pre_randomize();
    foreach (riscv_instr_pkg::supported_privileged_mode[i]) begin
      if(riscv_instr_pkg::supported_privileged_mode[i] == SUPERVISOR_MODE)
        support_supervisor_mode = 1;
    end
  endfunction

  function void post_randomize();
    // Setup the list all reserved registers
    reserved_regs = {default_reserved_regs, loop_regs};
    // Need to save all loop registers, and RA/T0
    min_stack_len_per_program = (max_nested_loop * 2 + 2) * (XLEN/8);
    // Check if the setting is legal
    check_setting();
  endfunction

  function void check_setting();
    bit support_64b;
    bit support_128b;
    foreach (riscv_instr_pkg::supported_isa[i]) begin
      if (riscv_instr_pkg::supported_isa[i] inside {RV64I, RV64M, RV64A, RV64F, RV64D, RV64C}) begin
        support_64b = 1'b1;
      end else if (riscv_instr_pkg::supported_isa[i] inside {RV128I, RV128C}) begin
        support_128b = 1'b1;
      end
    end
    if (support_128b && XLEN != 128) begin
      `uvm_fatal(`gfn, "XLEN should be set to 128 based on riscv_instr_pkg::supported_isa setting")
    end
    if (!support_128b && support_64b && XLEN != 64) begin
      `uvm_fatal(`gfn, "XLEN should be set to 64 based on riscv_instr_pkg::supported_isa setting")
    end
    if (!(support_128b || support_64b) && XLEN != 32) begin
      `uvm_fatal(`gfn, "XLEN should be set to 32 based on riscv_instr_pkg::supported_isa setting")
    end
    if (!(support_128b || support_64b) && !(SATP_MODE inside {SV32, BARE})) begin
      `uvm_fatal(`gfn, $sformatf("SATP mode %0s is not supported for RV32G ISA", SATP_MODE.name()))
    end
  endfunction

  // Get an integer argument from comand line
  function void get_int_arg_value(string cmdline_str, ref int val);
    string s;
    if(inst.get_arg_value(cmdline_str, s)) begin
      val = s.atoi();
    end
  endfunction

  // Get a bool argument from comand line
  function void get_bool_arg_value(string cmdline_str, ref bit val);
    string s;
    if(inst.get_arg_value(cmdline_str, s)) begin
      val = s.atobin();
    end
  endfunction

  // Get a hex argument from command line
  function void get_hex_arg_value(string cmdline_str, ref int val);
    string s;
    if(inst.get_arg_value(cmdline_str, s)) begin
      val = s.atohex();
    end
  endfunction

  // Build instruction template
  virtual function void build_instruction_template();
    riscv_instr_name_t instr_name;
    riscv_instr_name_t excluded_instr[$];
    get_excluded_instr(excluded_instr);
    instr_name = instr_name.first;
    do begin
      riscv_instr_base instr;
      if (!(instr_name inside {unsupported_instr, excluded_instr})) begin
        instr = riscv_instr_base::type_id::create("instr");
        `DV_CHECK_RANDOMIZE_WITH_FATAL(instr, instr_name == local::instr_name;)
        if (instr.group inside {supported_isa}) begin
          `uvm_info(`gfn, $sformatf("Adding [%s] %s to the list",
                          instr.group.name(), instr.instr_name.name()), UVM_HIGH)
          if (instr.category inside {SHIFT, ARITHMETIC, LOGICAL, COMPARE}) begin
            basic_instr.push_back(instr_name);
          end
          instr_group[instr.group].push_back(instr_name);
          instr_category[instr.category].push_back(instr_name);
          instr_template[instr_name] = instr;
        end
      end
      instr_name = instr_name.next;
    end
    while (instr_name != instr_name.first);
    if (no_ebreak == 0) begin
      basic_instr = {basic_instr, EBREAK};
    end
    if (no_fence == 0) begin
      basic_instr = {basic_instr, instr_category[SYNCH]};
    end
    // TODO: Support CSR instruction in other mode
    if ((no_csr_instr == 0) && (init_privileged_mode == MACHINE_MODE)) begin
      basic_instr = {basic_instr, instr_category[CSR]};
    end
    if (no_wfi == 0) begin
      basic_instr = {basic_instr, WFI};
    end
  endfunction

  virtual function void get_excluded_instr(ref riscv_instr_name_t excluded[$]);
    excluded = {excluded, INVALID_INSTR};
    // Below instrutions will modify stack pointer, not allowed in normal instruction stream.
    // It can be used in stack operation instruction stream.
    excluded = {excluded, C_SWSP, C_SDSP, C_ADDI16SP};
    if (!enable_sfence) begin
      excluded = {excluded, SFENCE_VMA};
    end
    if (no_fence) begin
      excluded = {excluded, FENCE, FENCEI, SFENCE_VMA};
    end
    // TODO: Support C_ADDI4SPN
    excluded = {excluded, C_ADDI4SPN};
  endfunction

endclass
