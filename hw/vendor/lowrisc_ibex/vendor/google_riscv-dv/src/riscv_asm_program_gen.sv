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

//-----------------------------------------------------------------------------------------
// RISC-V assembly program generator
//
// This is the main class to generate a complete RISC-V program, including the init routine,
// instruction section, data section, stack section, page table, interrupt and exception
// handling etc. Check gen_program() function to see how the program is generated.
//-----------------------------------------------------------------------------------------

class riscv_asm_program_gen extends uvm_object;

   riscv_instr_gen_config              cfg;
   riscv_data_page_gen                 data_page_gen;
   // User mode programs
   riscv_instr_sequence                main_program;
   riscv_instr_sequence                sub_program[];
   riscv_instr_sequence                debug_program;
   riscv_instr_sequence                debug_sub_program[];
   string                              instr_binary[$];
   // Kernel programs
   // These programs are called in the interrupt/exception handling routine based on the privileged
   // mode settings. For example, when the interrupt/exception is delegated to S-mode, if both SUM
   // and MPRV equal 1, kernel program can fetch/load/store from U-mode pages,
   // smode_accessible_umode_program is designed for this purpose. There can be other cases that
   // instruction can only be fetched from S-mode pages but load/store can access U-mode pages, or
   // everything needs to be in S-mode pages.
   riscv_instr_sequence                smode_accessible_umode_program;
   riscv_instr_sequence                smode_program;
   riscv_instr_sequence                smode_ls_umem_program;
   riscv_instr_stream                  directed_instr[];
   string                              instr_stream[$];
   riscv_callstack_gen                 callstack_gen;
   riscv_privileged_common_seq         privil_seq;
   // Directed instruction ratio, occurance per 1000 instructions
   int unsigned                        directed_instr_stream_ratio[string];
   riscv_page_table_list#(SATP_MODE)   page_table_list;

  `uvm_object_utils(riscv_asm_program_gen)

  function new (string name = "");
    super.new(name);
  endfunction

  //---------------------------------------------------------------------------------------
  // Main function to generate the whole program
  //---------------------------------------------------------------------------------------

  // This is the main function to generate all sections of the program.
  virtual function void gen_program();
    string sub_program_name[$];
    instr_stream.delete();
    // Generate program header
    gen_program_header();
    // Initialize general purpose registers
    init_gpr();
    if (!cfg.bare_program_mode) begin
      setup_misa();
      // Create all page tables
      create_page_table();
      // Setup privileged mode registers and enter target privileged mode
      pre_enter_privileged_mode();
    end
    // Init section
    gen_init_section();
    // Generate sub program
    gen_sub_program(sub_program, sub_program_name, cfg.num_of_sub_program);
    // Generate main program
    main_program = riscv_instr_sequence::type_id::create("main_program");
    main_program.instr_cnt = cfg.main_program_instr_cnt;
    main_program.is_debug_program = 0;
    main_program.label_name = "_main";
    generate_directed_instr_stream(.label("main"),
                                   .original_instr_cnt(main_program.instr_cnt),
                                   .min_insert_cnt(1),
                                   .instr_stream(main_program.directed_instr));
    main_program.cfg = cfg;
    `DV_CHECK_RANDOMIZE_FATAL(main_program)
    main_program.gen_instr(1);
    // Setup jump instruction among main program and sub programs
    gen_callstack(main_program, sub_program, sub_program_name, cfg.num_of_sub_program);
    `uvm_info(`gfn, "Generating callstack...done", UVM_LOW)
    main_program.post_process_instr();
    `uvm_info(`gfn, "Post-processing main program...done", UVM_LOW)
    main_program.generate_instr_stream();
    `uvm_info(`gfn, "Generating main program instruction stream...done", UVM_LOW)
    instr_stream = {instr_stream, main_program.instr_string_list};
    // Test done section
    gen_test_done();
    // Shuffle the sub programs and insert to the instruction stream
    insert_sub_program(sub_program, instr_stream);
    `uvm_info(`gfn, "Inserting sub-programs...done", UVM_LOW)
    // Reserve some space to copy instruction from data section
    if (instr_binary.size() > 0) begin
      instr_stream.push_back(".align 2");
      instr_stream.push_back("sub_bin:");
      instr_stream.push_back({indent, $sformatf(".rept %0d", 2 * instr_binary.size())});
      instr_stream.push_back({indent, "nop"});
      instr_stream.push_back({indent, ".endr"});
      instr_stream.push_back({indent, "ret"});
    end
    `uvm_info(`gfn, "Main/sub program generation...done", UVM_LOW)
    // Program end
    gen_program_end();
    if (!cfg.bare_program_mode) begin
      // Privileged mode switch routine
      gen_privileged_mode_switch_routine();
      // Generate debug rom section
      gen_debug_rom();
      // Generate debug mode exception handler
      gen_debug_exception_handler();
    end
    // Starting point of data section
    gen_data_page_begin();
    // Page table
    if (!cfg.bare_program_mode) begin
      gen_page_table_section();
    end
    if(!cfg.no_data_page) begin
      // Kernel data section
      gen_data_page();
    end
    gen_data_page_end();
    // Stack section
    gen_stack_section();
    if (!cfg.bare_program_mode) begin
      // Generate kernel program/data/stack section
      gen_kernel_sections();
    end
  endfunction

  //---------------------------------------------------------------------------------------
  // Generate kernel program/data/stack sections
  //---------------------------------------------------------------------------------------
  virtual function void gen_kernel_sections();
    instr_stream.push_back("_kernel_instr_start: .align 12");
    instr_stream.push_back(".text");
    // Kernel programs
    if (cfg.virtual_addr_translation_on) begin
      smode_accessible_umode_program = riscv_instr_sequence::type_id::
                                       create("smode_accessible_umode_program");
      gen_kernel_program(smode_accessible_umode_program);
      smode_program = riscv_instr_sequence::type_id::create("smode_program");
      gen_kernel_program(smode_program);
      smode_ls_umem_program = riscv_instr_sequence::type_id::create("smode_ls_umem_program");
      gen_kernel_program(smode_ls_umem_program);
    end
    // All trap/interrupt handling is in the kernel region
    // Trap/interrupt delegation to user mode is not supported now
    // Trap handler
    gen_all_trap_handler();
    // Interrupt handling subroutine
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      gen_interrupt_handler_section(riscv_instr_pkg::supported_privileged_mode[i]);
    end
    instr_stream.push_back("_kernel_instr_end: nop");
    // User stack and data pages may not be accessible when executing trap handling programs in
    // machine/supervisor mode. Generate separate kernel data/stack sections to solve it.
    if (cfg.virtual_addr_translation_on) begin
      // Kernel data pages
      instr_stream.push_back("_kernel_data_start: .align 12");
      if(!cfg.no_data_page) begin
        // Data section
        gen_data_page(1'b1);
      end
      gen_data_page_end();
    end
    // Kernel stack section
    gen_kernel_stack_section();
  endfunction

  virtual function void gen_kernel_program(riscv_instr_sequence seq);
    seq.instr_cnt = cfg.kernel_program_instr_cnt;
    generate_directed_instr_stream(.label(seq.get_name()),
                                   .original_instr_cnt(seq.instr_cnt),
                                   .min_insert_cnt(0),
                                   .instr_stream(seq.directed_instr),
                                   .kernel_mode(1'b1));
    seq.label_name = seq.get_name();
    seq.is_debug_program = 0;
    seq.cfg = cfg;
    `DV_CHECK_RANDOMIZE_FATAL(seq)
    seq.gen_instr(0);
    seq.post_process_instr();
    seq.generate_instr_stream();
    instr_stream = {instr_stream, seq.instr_string_list};
  endfunction

  //---------------------------------------------------------------------------------------
  // Generate any subprograms and set up the callstack
  //---------------------------------------------------------------------------------------

  virtual function void gen_sub_program(ref riscv_instr_sequence sub_program[],
                                        ref string sub_program_name[$],
                                        input int num_sub_program,
                                        bit is_debug = 1'b0,
                                        string prefix = "sub");
    if(num_sub_program > 0) begin
      sub_program = new[num_sub_program];
      foreach(sub_program[i]) begin
        sub_program[i] = riscv_instr_sequence::type_id::create($sformatf("%s_%0d",prefix,i+1));
        `uvm_info(`gfn, $sformatf("sub program name: %s", prefix), UVM_LOW)
        sub_program[i].is_debug_program = is_debug;
        if (is_debug) begin
          sub_program[i].instr_cnt = cfg.debug_sub_program_instr_cnt[i];
        end else begin
          sub_program[i].instr_cnt = cfg.sub_program_instr_cnt[i];
        end
        generate_directed_instr_stream(.label(sub_program[i].get_name()),
                                       .original_instr_cnt(sub_program[i].instr_cnt),
                                       .min_insert_cnt(0),
                                       .instr_stream(sub_program[i].directed_instr));
        sub_program[i].label_name = sub_program[i].get_name();
        sub_program[i].cfg = cfg;
        `DV_CHECK_RANDOMIZE_FATAL(sub_program[i])
        sub_program[i].gen_instr(0);
        sub_program_name.push_back(sub_program[i].label_name);
      end
    end
  endfunction

  virtual function void gen_callstack(riscv_instr_sequence main_program,
                                      ref riscv_instr_sequence sub_program[],
                                      ref string sub_program_name[$],
                                      input int num_sub_program);
    if(num_sub_program != 0) begin
      callstack_gen = riscv_callstack_gen::type_id::create("callstack_gen");
      callstack_gen.init(num_sub_program+1);
      `uvm_info(get_full_name(), "Randomizing call stack", UVM_LOW)
      if(callstack_gen.randomize()) begin
        program_id_t pid;
        int idx;
        // Insert the jump instruction based on the call stack
        foreach(callstack_gen.program_h[i]) begin
          foreach(callstack_gen.program_h[i].sub_program_id[j]) begin
            idx++;
            pid = callstack_gen.program_h[i].sub_program_id[j] - 1;
            `uvm_info(get_full_name(), $sformatf(
                      "Gen jump instr %0d -> sub[%0d] %0d", i, j, pid+1), UVM_LOW)
            if(i == 0)
              main_program.insert_jump_instr(sub_program_name[pid], idx);
            else
              sub_program[i-1].insert_jump_instr(sub_program_name[pid], idx);
          end
        end
      end else begin
        `uvm_fatal(get_full_name(), "Failed to generate callstack")
      end
    end
    `uvm_info(get_full_name(), "Randomizing call stack..done", UVM_LOW)
  endfunction

  virtual function void insert_sub_program(ref riscv_instr_sequence sub_program[],
                                           ref string instr_list[$]);
    sub_program.shuffle();
    foreach(sub_program[i]) begin
      sub_program[i].post_process_instr();
      sub_program[i].generate_instr_stream();
      instr_list = {instr_list, sub_program[i].instr_string_list};
    end
  endfunction

  //---------------------------------------------------------------------------------------
  // Major sections - init, stack, data, test_done etc.
  //---------------------------------------------------------------------------------------

  virtual function void gen_program_header();
    instr_stream.push_back(".include \"user_define.h\"");
    instr_stream.push_back(".globl _start");
    instr_stream.push_back(".section .text");
    instr_stream.push_back("_start:");
  endfunction

  virtual function void gen_program_end();
    // Use write_tohost to terminate spike simulation
    gen_section("write_tohost", {"sw gp, tohost, t5"});
    gen_section("_exit", {"j write_tohost"});
  endfunction

  virtual function void gen_data_page_begin();
    instr_stream.push_back(".data");
    instr_stream.push_back(".pushsection .tohost,\"aw\",@progbits;");
    instr_stream.push_back(".align 6; .global tohost; tohost: .dword 0;");
    instr_stream.push_back(".align 6; .global fromhost; fromhost: .dword 0;");
    instr_stream.push_back(".popsection;");
  endfunction

  virtual function void gen_data_page(bit is_kernel = 1'b0);
    string data_page;
    data_page_gen = riscv_data_page_gen::type_id::create("data_page_gen");
    data_page_gen.cfg = cfg;
    data_page_gen.gen_data_page(cfg.data_page_pattern, is_kernel);
    instr_stream = {instr_stream, data_page_gen.data_page_str};
  endfunction

  virtual function void gen_data_page_end();
    instr_stream.push_back(".align 4;");
  endfunction

  // Generate the user stack section
  virtual function void gen_stack_section();
    instr_stream.push_back(".pushsection .user_stack,\"aw\",@progbits;");
    instr_stream.push_back(".align 12");
    instr_stream.push_back("_user_stack_start:");
    instr_stream.push_back($sformatf(".rept %0d", cfg.stack_len - 1));
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    instr_stream.push_back(".endr");
    instr_stream.push_back("_user_stack_end:");
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    instr_stream.push_back(".popsection;");
  endfunction

  // The kernal stack is used to save user program context before executing exception handling
  virtual function void gen_kernel_stack_section();
    instr_stream.push_back(".pushsection .kernel_stack,\"aw\",@progbits;");
    instr_stream.push_back(".align 12");
    instr_stream.push_back("_kernel_stack_start:");
    instr_stream.push_back($sformatf(".rept %0d", cfg.kernel_stack_len - 1));
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    instr_stream.push_back(".endr");
    instr_stream.push_back("_kernel_stack_end:");
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    instr_stream.push_back(".popsection;");
  endfunction

  virtual function void gen_init_section();
    string str;
    str = format_string("_init:", LABEL_STR_LEN);
    instr_stream.push_back(str);
    // Init stack pointer to point to the end of the user stack
    str = {indent, "la sp, _user_stack_end"};
    instr_stream.push_back(str);
    core_is_initialized();
    // Copy the instruction from data section to instruction section
    if (instr_binary.size() > 0) begin
      instr_stream.push_back({indent, "la x31, instr_bin"});
      instr_stream.push_back({indent, "la x30, sub_bin"});
      instr_stream.push_back({indent, $sformatf(".rept %0d", instr_binary.size())});
      instr_stream.push_back({indent, "lw x29, 0(x31)"});
      instr_stream.push_back({indent, "sw x29, 0(x30)"});
      instr_stream.push_back({indent, "addi x31, x31, 4"});
      instr_stream.push_back({indent, "addi x30, x30, 4"});
      instr_stream.push_back({indent, ".endr"});
    end
  endfunction

  // Setup MISA based on supported extensions
  virtual function void setup_misa();
    bit [XLEN-1:0] misa;
    misa[XLEN-1:XLEN-3] = (XLEN == 32) ? 1 :
                          (XLEN == 64) ? 2 : 3;
    if (cfg.check_misa_init_val) begin
      instr_stream.push_back({indent, "csrr x15, misa"});
    end
    foreach (supported_isa[i]) begin
      case (supported_isa[i]) inside
        RV32C, RV64C, RV128C : misa[MISA_EXT_C] = 1'b1;
        RV32I, RV64I, RV128I : misa[MISA_EXT_I] = 1'b1;
        RV32M, RV64M         : misa[MISA_EXT_M] = 1'b1;
        RV32A, RV64A         : misa[MISA_EXT_A] = 1'b1;
        default : `uvm_fatal(`gfn, $sformatf("%0s is not yet supported", supported_isa[i].name()))
      endcase
    end
    if (SUPERVISOR_MODE inside {supported_privileged_mode}) begin
      misa[MISA_EXT_S] = 1'b1;
    end
    instr_stream.push_back({indent, $sformatf("li x15, 0x%0x", misa)});
    instr_stream.push_back({indent, "csrw misa, x15"});
  endfunction

  // Write to the signature_addr with values to indicate to the core testbench
  // that is safe to start sending interrupt and debug stimulus
  virtual function void core_is_initialized();
    string instr[$];
    if (cfg.require_signature_addr) begin
      if (cfg.signature_addr != 32'hdead_beef) begin
        gen_signature_handshake(instr, CORE_STATUS, INITIALIZED);
        format_section(instr);
        instr_stream = {instr_stream, instr};
      end else begin
        `uvm_fatal(`gfn, "The signature_addr is not properly configured!")
      end
    end
  endfunction

  // Initialize general purpose registers with random value
  virtual function void init_gpr();
    string str;
    bit [DATA_WIDTH-1:0] reg_val;
    // Init general purpose registers with random values
    for(int i = 0; i < 32; i++) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(reg_val,
        reg_val dist {
          'h0                         :/ 1,
          'h8000_0000                 :/ 1,
          ['h1         : 'hF]         :/ 1,
          ['h10        : 'hEFFF_FFFF] :/ 1,
          ['hF000_0000 : 'hFFFF_FFFF] :/ 1
        };)
      str = $sformatf("%0sli x%0d, 0x%0x", indent, i, reg_val);
      instr_stream.push_back(str);
    end
  endfunction

  // Generate "test_done" section, test is finished by an ECALL instruction
  // The ECALL trap handler will handle the clean up procedure before finishing the test.
  virtual function void gen_test_done();
    string str = format_string("test_done:", LABEL_STR_LEN);
    instr_stream.push_back(str);
    instr_stream.push_back({indent, "li gp, 1"});
    if (cfg.bare_program_mode) begin
      instr_stream.push_back({indent, "j write_tohost"});
    end else begin
      instr_stream.push_back({indent, "ecall"});
    end
  endfunction

  // Dump all GPR to the starting point of the program
  // TB can check the GPR value for this memory location to compare with expected value generated
  // by the ISA simulator. If the processor doesn't have a good tracer unit, it might not be
  // possible to compare the GPR value after each instruction execution.
  virtual function void gen_register_dump();
    string str;
    riscv_reg_t base_address_reg;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(base_address_reg, base_address_reg != ZERO;)
    // Load base address
    str = {indent, $sformatf("la x%0d, _start", base_address_reg)};
    instr_stream.push_back(str);
    // Generate sw/sd instructions
    for(int i = 0; i < 32; i++) begin
      if(XLEN == 64) begin
        str = {indent, $sformatf("sd x%0d, %0d(x%0d)", i, i*(XLEN/8), base_address_reg)};
      end else begin
        str = {indent, $sformatf("sw x%0d, %0d(x%0d)", i, i*(XLEN/8), base_address_reg)};
      end
      instr_stream.push_back(str);
    end
  endfunction

  //---------------------------------------------------------------------------------------
  // Privileged mode entering routine
  //---------------------------------------------------------------------------------------

  virtual function void pre_enter_privileged_mode();
    string instr[];
    // Setup kerenal stack pointer
    gen_section("kernel_sp", {"la tp, _kernel_stack_end"});
    // Setup interrupt and exception delegation
    if(!cfg.no_delegation && (cfg.init_privileged_mode != MACHINE_MODE)) begin
      gen_delegation();
    end
    // Setup trap vector register
    trap_vector_init();
    // Initialize PTE (link page table based on their real physical address)
    if(cfg.virtual_addr_translation_on) begin
      page_table_list.process_page_table(instr);
      gen_section("process_pt", instr);
    end
    // Setup mepc register, jump to init entry
    setup_epc();
  endfunction

  virtual function void gen_privileged_mode_switch_routine();
    privil_seq = riscv_privileged_common_seq::type_id::create("privil_seq");
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      string instr[$];
      string csr_handshake[$];
      string ret_instr;
      if(riscv_instr_pkg::supported_privileged_mode[i] < cfg.init_privileged_mode) continue;
      `uvm_info(`gfn, $sformatf("Generating privileged mode routing for %0s",
                      riscv_instr_pkg::supported_privileged_mode[i].name()), UVM_LOW)
      // Enter privileged mode
      privil_seq.cfg = cfg;
      `DV_CHECK_RANDOMIZE_FATAL(privil_seq)
      privil_seq.enter_privileged_mode(riscv_instr_pkg::supported_privileged_mode[i], instr);
      if (cfg.require_signature_addr) begin
        ret_instr = instr.pop_back();
        // Want to write the main system CSRs to the testbench before indicating that initialization
        // is complete, for any initial state analysis
        case(riscv_instr_pkg::supported_privileged_mode[i])
          MACHINE_MODE: begin
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(MSTATUS));
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(MIE));
          end
          SUPERVISOR_MODE: begin
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(SSTATUS));
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(SIE));
          end
          USER_MODE: begin
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(USTATUS));
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(UIE));
          end
        endcase
        format_section(csr_handshake);
        instr = {instr, csr_handshake, ret_instr};
      end
      instr_stream = {instr_stream, instr};
    end
  endfunction

  // Setup EPC before entering target privileged mode
  virtual function void setup_epc();
    string instr[];
    string mode_name;
    instr = {"la x10, _init"};
    if(cfg.virtual_addr_translation_on) begin
      // For supervisor and user mode, use virtual address instead of physical address.
      // Virtual address starts from address 0x0, here only the lower 12 bits are kept
      // as virtual address offset.
      instr = {instr,
               $sformatf("slli x10, x10, %0d", XLEN - 12),
               $sformatf("srli x10, x10, %0d", XLEN - 12)};
    end
    mode_name = cfg.init_privileged_mode.name();
    instr = {instr,
             "csrw mepc, x10",
             $sformatf("j init_%0s", mode_name.tolower())
            };
    gen_section("mepc_setup", instr);
  endfunction

  //---------------------------------------------------------------------------------------
  // Privileged CSR setup for interrupt and exception handling and delegation
  //---------------------------------------------------------------------------------------

  // Interrupt and exception delegation setting.
  // The lower level exception and interrupt can be delegated to higher level handler.
  virtual function void gen_delegation();
    gen_delegation_instr(MEDELEG, MIDELEG,
                         cfg.m_mode_exception_delegation,
                         cfg.m_mode_interrupt_delegation);
    if(riscv_instr_pkg::support_umode_trap) begin
      gen_delegation_instr(SEDELEG, SIDELEG,
                           cfg.s_mode_exception_delegation,
                           cfg.s_mode_interrupt_delegation);
    end
  endfunction

  virtual function void gen_delegation_instr(privileged_reg_t edeleg,
                                             privileged_reg_t ideleg,
                                             bit edeleg_enable[exception_cause_t],
                                             bit ideleg_enable[interrupt_cause_t]);
    bit [XLEN-1:0] deleg_val;
    string section_name;
    string instr[];
    // Exception delegation setup
    foreach(edeleg_enable[cause]) begin
      if(edeleg_enable[cause]) begin
        deleg_val = deleg_val | (1 << int'(cause));
      end
    end
    instr = {$sformatf("li a0, 0x%0x", deleg_val),
             $sformatf("csrw 0x%0x, a0 # %0s", edeleg, edeleg.name())};
    // Interrupt delegation setup
    deleg_val = '0;
    foreach(ideleg_enable[cause]) begin
      if(ideleg_enable[cause]) begin
        deleg_val = deleg_val | (1 << int'(cause));
      end
    end
    instr = {instr,
             $sformatf("li a0, 0x%0x", deleg_val),
             $sformatf("csrw 0x%0x, a0 # %0s", ideleg, ideleg.name())};
    section_name = edeleg.name();
    section_name = section_name.tolower();
    gen_section($sformatf("%0s_setup", section_name), instr);
  endfunction

  // Setup trap vector - MTVEC, STVEC, UTVEC
  virtual function void trap_vector_init();
    string instr[];
    privileged_reg_t trap_vec_reg;
    string tvec_name;
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      case(riscv_instr_pkg::supported_privileged_mode[i])
        MACHINE_MODE:    trap_vec_reg = MTVEC;
        SUPERVISOR_MODE: trap_vec_reg = STVEC;
        USER_MODE:       trap_vec_reg = UTVEC;
      endcase
      // Skip utvec init if trap delegation to u_mode is not supported
      if ((riscv_instr_pkg::supported_privileged_mode[i] == USER_MODE) &&
          !riscv_instr_pkg::support_umode_trap) continue;
      if (riscv_instr_pkg::supported_privileged_mode[i] < cfg.init_privileged_mode) continue;
      tvec_name = trap_vec_reg.name();
      instr = {instr, $sformatf("la a0, %0s_handler", tvec_name.tolower())};
      if (SATP_MODE != BARE && riscv_instr_pkg::supported_privileged_mode[i] != MACHINE_MODE) begin
        // For supervisor and user mode, use virtual address instead of physical address.
        // Virtual address starts from address 0x0, here only the lower 20 bits are kept
        // as virtual address offset.
        instr = {instr,
                 $sformatf("slli a0, a0, %0d", XLEN - 20),
                 $sformatf("srli a0, a0, %0d", XLEN - 20)};
      end
      instr = {instr, $sformatf("ori a0, a0, %0d", cfg.mtvec_mode)};
      instr = {instr, $sformatf("csrw 0x%0x, a0 # %0s", trap_vec_reg, trap_vec_reg.name())};
    end
    gen_section("trap_vec_init", instr);
  endfunction

  //---------------------------------------------------------------------------------------
  // Exception handling routine
  //---------------------------------------------------------------------------------------

  // Trap handling routine
  virtual function void gen_all_trap_handler();
    string instr[$];
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      if(riscv_instr_pkg::supported_privileged_mode[i] < cfg.init_privileged_mode) continue;
      case(riscv_instr_pkg::supported_privileged_mode[i])
        MACHINE_MODE:
          gen_trap_handler_section("m", MCAUSE, MTVEC, MTVAL, MEPC, MSCRATCH, MSTATUS, MIE, MIP);
        SUPERVISOR_MODE:
          gen_trap_handler_section("s", SCAUSE, STVEC, STVAL, SEPC, SSCRATCH, SSTATUS, SIE, SIP);
        USER_MODE:
          if(riscv_instr_pkg::support_umode_trap)
            gen_trap_handler_section("u", UCAUSE, UTVEC, UTVAL, UEPC, USCRATCH, USTATUS, UIE, UIP);
      endcase
    end
    // Ebreak handler
    gen_ebreak_handler();
    // Ecall handler
    gen_ecall_handler();
    // Illegal instruction handler
    gen_illegal_instr_handler();
    // Instruction fault handler
    gen_instr_fault_handler();
    // Load fault handler
    gen_load_fault_handler();
    // Store fault handler
    gen_store_fault_handler();
    // Generate page table fault handling routine
    // Page table fault is always handled in machine mode, as virtual address translation may be
    // broken when page fault happens.
    gen_signature_handshake(instr, CORE_STATUS, HANDLING_EXCEPTION);
    if(page_table_list != null) begin
      page_table_list.gen_page_fault_handling_routine(instr);
    end else begin
      instr.push_back("nop");
    end
    gen_section("pt_fault_handler", instr);
  endfunction

  // Generate the interrupt and trap handler for different privileged mode.
  // The trap handler checks the xCAUSE to determine the type of the exception and jumps to
  // corresponding exeception handling routine.
  virtual function void gen_trap_handler_section(string mode,
                                            privileged_reg_t cause, privileged_reg_t tvec,
                                            privileged_reg_t tval, privileged_reg_t epc,
                                            privileged_reg_t scratch, privileged_reg_t status,
                                            privileged_reg_t ie, privileged_reg_t ip);
    bit is_interrupt = 'b1;
    string tvec_name;
    string instr[$];
    if (cfg.mtvec_mode == VECTORED) begin
      gen_interrupt_vector_table(mode, status, cause, ie, ip, scratch, instr);
    end else begin
      // Push user mode GPR to kernel stack before executing exception handling, this is to avoid
      // exception handling routine modify user program state unexpectedly
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, instr);
      // Checking xStatus can be optional if ISS (like spike) has different implementation of certain
      // fields compared with the RTL processor.
      if (cfg.check_xstatus) begin
        instr = {instr, $sformatf("csrr x15, 0x%0x # %0s", status, status.name())};
      end
      instr = {instr,
               // Use scratch CSR to save a GPR value
               // Check if the exception is caused by an interrupt, if yes, jump to interrupt handler
               // Interrupt is indicated by xCause[XLEN-1]
               $sformatf("csrr a1, 0x%0x # %0s", cause, cause.name()),
               $sformatf("srli a1, a1, %0d", XLEN-1),
               $sformatf("bne a1, x0, %0smode_intr_handler", mode)};
    end
    // The trap handler will occupy one 4KB page, it will be allocated one entry in the page table
    // with a specific privileged mode.
    instr_stream.push_back(".align 12");
    tvec_name = tvec.name();
    gen_section($sformatf("%0s_handler", tvec_name.tolower()), instr);
    // Exception handler
    instr = {};
    if (cfg.mtvec_mode == VECTORED) begin
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, instr);
    end
    gen_signature_handshake(instr, CORE_STATUS, HANDLING_EXCEPTION);
    instr = {instr,
             // The trap is caused by an exception, read back xCAUSE, xEPC to see if these
             // CSR values are set properly. The checking is done by comparing against the log
             // generated by ISA simulator (spike).
             $sformatf("csrr a1, 0x%0x # %0s", cause, cause.name()),
             $sformatf("csrr x31, 0x%0x # %0s", epc, epc.name()),
             // Breakpoint
             $sformatf("li a2, 0x%0x # BREAKPOINT", BREAKPOINT),
             "beq a1, a2, ebreak_handler",
             // Check if it's an ECALL exception. Jump to ECALL exception handler
             $sformatf("li a2, 0x%0x # ECALL_UMODE", ECALL_UMODE),
             "beq a1, a2, ecall_handler",
             $sformatf("li a2, 0x%0x # ECALL_SMODE", ECALL_SMODE),
             "beq a1, a2, ecall_handler",
             $sformatf("li a2, 0x%0x # ECALL_MMODE", ECALL_MMODE),
             "beq a1, a2, ecall_handler",
             // Page table fault or access fault conditions
             $sformatf("li a2, 0x%0x", INSTRUCTION_ACCESS_FAULT),
             "beq a1, a2, instr_fault_handler",
             $sformatf("li a2, 0x%0x", LOAD_ACCESS_FAULT),
             "beq a1, a2, load_fault_handler",
             $sformatf("li a2, 0x%0x", STORE_AMO_ACCESS_FAULT),
             "beq a1, a2, store_fault_handler",
             $sformatf("li a2, 0x%0x", INSTRUCTION_PAGE_FAULT),
             "beq a1, a2, pt_fault_handler",
             $sformatf("li a2, 0x%0x", LOAD_PAGE_FAULT),
             "beq a1, a2, pt_fault_handler",
             $sformatf("li a2, 0x%0x", STORE_AMO_PAGE_FAULT),
             "beq a1, a2, pt_fault_handler",
             // Illegal instruction exception
             $sformatf("li a2, 0x%0x # ILLEGAL_INSTRUCTION", ILLEGAL_INSTRUCTION),
             "beq a1, a2, illegal_instr_handler",
             // Skip checking tval for illegal instruction as it's implementation specific
             $sformatf("csrr x30, 0x%0x # %0s", tval, tval.name()),
             "1: jal x1, test_done "
           };
    gen_section($sformatf("%0smode_exception_handler", mode), instr);
  endfunction

  // Generate for interrupt vector table
  virtual function void gen_interrupt_vector_table(string           mode,
                                                   privileged_reg_t status,
                                                   privileged_reg_t cause,
                                                   privileged_reg_t ie,
                                                   privileged_reg_t ip,
                                                   privileged_reg_t scratch,
                                                   ref string       instr[$]);

    // In vector mode, the BASE address is shared between interrupt 0 and exception handling.
    // When vectored interrupts are enabled, interrupt cause 0, which corresponds to user-mode
    // software interrupts, are vectored to the same location as synchronous exceptions. This
    // ambiguity does not arise in practice, since user-mode software interrupts are either
    // disabled or delegated
    instr = {instr, ".option norvc;",
                    $sformatf("j %0smode_exception_handler", mode)};
    // Redirect the interrupt to the corresponding interrupt handler
    for (int i = 1; i < max_interrupt_vector_num; i++) begin
      instr.push_back($sformatf("j %0smode_intr_vector_%0d", mode, i));
    end
    instr = {instr, ".option rvc;"};
    for (int i = 1; i < max_interrupt_vector_num; i++) begin
      string intr_handler[$];
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, intr_handler);
      gen_signature_handshake(.instr(intr_handler), .signature_type(CORE_STATUS), .core_status(HANDLING_IRQ));
      intr_handler = {intr_handler,
                      $sformatf("csrr a1, 0x%0x # %0s", cause, cause.name()),
                      // Terminate the test if xCause[31] != 0 (indicating exception)
                      $sformatf("srli a1, a1, 0x%0x", XLEN-1),
                      $sformatf("beqz a1, 1f")};
      gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(status));
      gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(cause));
      gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(ie));
      gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(ip));
               // Jump to commmon interrupt handling routine
      intr_handler = {intr_handler,
                      $sformatf("j %0smode_intr_handler", mode),
                      "1: j test_done"};
      gen_section($sformatf("%0smode_intr_vector_%0d", mode, i), intr_handler);
    end
  endfunction

  // ECALL trap handler
  // It does some clean up like dump GPRs before communicating with host to terminate the test.
  // User can extend this function if some custom clean up routine is needed.
  virtual function void gen_ecall_handler();
    string str;
    str = format_string("ecall_handler:", LABEL_STR_LEN);
    instr_stream.push_back(str);
    dump_perf_stats();
    gen_register_dump();
    str = format_string(" ", LABEL_STR_LEN);
    str = {str, "j write_tohost"};
    instr_stream.push_back(str);
  endfunction

  // Ebreak trap handler
  // When breakpoint exception happens, epc will be written with ebreak instruction
  // itself. Add epc by 4 and resume execution.
  // Note the breakpoint could be triggered by a C.EBREAK instruction, the generated program
  // guarantees that epc + 4 is a valid instruction boundary
  // TODO: Support random operations in debug mode
  // TODO: Support ebreak exception delegation
  // TODO: handshake the correct Xcause CSR based on delegation privil. mode
  virtual function void gen_ebreak_handler();
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, EBREAK_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    instr = {instr,
            "csrr  x31, mepc",
            "addi  x31, x31, 4",
            "csrw  mepc, x31"
    };
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, instr);
    instr.push_back("mret");
    gen_section("ebreak_handler", instr);
  endfunction

  // Illegal instruction handler
  // Note: Save the illegal instruction to MTVAL is optional in the spec, and mepc could be
  // a virtual address that cannot be used in machine mode handler. As a result, there's no way to
  // know the illegal instruction is compressed or not. This hanlder just simply adds the PC by
  // 4 and resumes execution. The way that the illegal instruction is injected guarantees that
  // PC + 4 is a valid instruction boundary.
  // TODO: handshake the corret Xcause CSR based on delegation setup
  virtual function void gen_illegal_instr_handler();
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, ILLEGAL_INSTR_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    instr = {instr,
            "csrr  x31, mepc",
            "addi  x31, x31, 4",
            "csrw  mepc, x31"
    };
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, instr);
    instr.push_back("mret");
    gen_section("illegal_instr_handler", instr);
  endfunction

  // TODO: handshake correct csr based on delegation
  virtual function void gen_instr_fault_handler();
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, INSTR_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, instr);
    instr.push_back("mret");
    gen_section("instr_fault_handler", instr);
  endfunction

  // TODO: handshake correct csr based on delegation
  virtual function void gen_load_fault_handler();
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, LOAD_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, instr);
    instr.push_back("mret");
    gen_section("load_fault_handler", instr);
  endfunction

  // TODO: handshake correct csr based on delegation
  virtual function void gen_store_fault_handler();
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, STORE_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, instr);
    instr.push_back("mret");
    gen_section("store_fault_handler", instr);
  endfunction

  //---------------------------------------------------------------------------------------
  // Page table setup
  //---------------------------------------------------------------------------------------

  // Create page table if virtual address translation is supported.
  // The page is created based on the address translation mode - SV32, SV39, SV48
  // Right now only the lowest level 4KB page table is configured as leaf page table entry (PTE),
  // all the other super pages are link PTE.
  virtual function void create_page_table();
    string instr[];
    if(cfg.virtual_addr_translation_on) begin
      page_table_list = riscv_page_table_list#(SATP_MODE)::
                        type_id::create("page_table_list");
      page_table_list.cfg = cfg;
      page_table_list.create_page_table_list();
      page_table_list.enable_exception = cfg.enable_page_table_exception;
      `uvm_info(`gfn, $sformatf("Randomizing page tables, totally %0d page tables, mode = %0s",
                      page_table_list.page_table.size(), cfg.init_privileged_mode.name()), UVM_LOW)
      page_table_list.privileged_mode = cfg.init_privileged_mode;
      `DV_CHECK_RANDOMIZE_FATAL(page_table_list);
      page_table_list.randomize_page_table();
      `uvm_info(`gfn, "Finished creating page tables", UVM_LOW)
    end
  endfunction

  // Generate the page table section of the program
  // The page table is generated as a group of continuous 4KB data sections.
  virtual function void gen_page_table_section();
    string page_table_section[$];
    if(page_table_list != null) begin
      instr_stream.push_back(".pushsection .page_table,\"aw\",@progbits;");
      foreach(page_table_list.page_table[i]) begin
        page_table_list.page_table[i].gen_page_table_section(page_table_section);
        instr_stream = {instr_stream, page_table_section};
      end
      instr_stream.push_back(".popsection;");
    end
  endfunction

  // Only extend this function if the core utilizes a PLIC for handling interrupts
  // In this case, the core will write to a specific location as the response to the interrupt, and
  // external PLIC unit can detect this response and process the interrupt clean up accordingly.
  virtual function void gen_plic_section(ref string interrupt_handler_instr[$]);
    // Utilize the memory mapped handshake scheme to signal the testbench that the interrupt
    // handling has been completed and we are about to xRET out of the handler
    gen_signature_handshake(.instr(interrupt_handler_instr), .signature_type(CORE_STATUS),
                            .core_status(FINISHED_IRQ));
  endfunction

  // Interrupt handler routine
  virtual function void gen_interrupt_handler_section(privileged_mode_t mode);
    string mode_prefix;
    string ls_unit;
    privileged_reg_t status, ip, ie, scratch;
    string interrupt_handler_instr[$];
    ls_unit = (XLEN == 32) ? "w" : "d";
    if(mode < cfg.init_privileged_mode) return;
    case(mode)
      MACHINE_MODE: begin
        mode_prefix = "m";
        status = MSTATUS;
        ip = MIP;
        ie = MIE;
        scratch = MSCRATCH;
      end
      SUPERVISOR_MODE: begin
        mode_prefix = "s";
        status = SSTATUS;
        ip = SIP;
        ie = SIE;
        scratch = SSCRATCH;
      end
      USER_MODE: begin
        mode_prefix = "u";
        status = USTATUS;
        ip = UIP;
        ie = UIE;
        scratch = USCRATCH;
      end
      default: `uvm_fatal(get_full_name(), $sformatf("Unsupported mode: %0s", mode.name()))
    endcase
    // Read back interrupt related privileged CSR
    // The value of these CSR are checked by comparing with spike simulation result.
    interrupt_handler_instr = {
           interrupt_handler_instr,
           $sformatf("csrr  a1, 0x%0x # %0s;", status, status.name()),
           $sformatf("csrr  a1, 0x%0x # %0s;", ie, ie.name()),
           $sformatf("csrr  a1, 0x%0x # %0s;", ip, ip.name()),
           // Clean all the pending interrupt
           $sformatf("csrrc a1, 0x%0x, a1 # %0s;", ip, ip.name())
    };
    gen_plic_section(interrupt_handler_instr);
    // Restore user mode GPR value from kernel stack before return
    pop_gpr_from_kernel_stack(status, scratch, cfg.mstatus_mprv, interrupt_handler_instr);
    interrupt_handler_instr = {interrupt_handler_instr,
                               $sformatf("%0sret;", mode_prefix)
    };
    // The interrupt handler will use one 4KB page
    instr_stream.push_back(".align 12");
    gen_section($sformatf("%0smode_intr_handler", mode_prefix), interrupt_handler_instr);
  endfunction

  //---------------------------------------------------------------------------------------
  // Helper functions
  //---------------------------------------------------------------------------------------

  // Format a code section, without generating it
  virtual function void format_section(ref string instr[$]);
    string prefix = format_string(" ", LABEL_STR_LEN);
    foreach(instr[i]) begin
      instr[i] = {prefix, instr[i]};
    end
  endfunction

  // Generate a code section
  virtual function void gen_section(string label, string instr[$]);
    string str;
    if(label != "") begin
      str = format_string($sformatf("%0s:", label), LABEL_STR_LEN);
      instr_stream.push_back(str);
    end
    foreach(instr[i]) begin
      str = {indent, instr[i]};
      instr_stream.push_back(str);
    end
    instr_stream.push_back("");
  endfunction

  // Dump performance CSRs if applicable
  virtual function void dump_perf_stats();
    foreach(implemented_csr[i]) begin
      if (implemented_csr[i] inside {[MCYCLE:MHPMCOUNTER31H]}) begin
        gen_signature_handshake(.instr(instr_stream), .signature_type(WRITE_CSR), .csr(implemented_csr[i]));
      end
    end
  endfunction

  // Write the generated program to a file
  function void gen_test_file(string test_name);
    int fd;
    fd = $fopen(test_name,"w");
    foreach(instr_stream[i]) begin
      $fwrite(fd, {instr_stream[i],"\n"});
    end
    $fclose(fd);
    `uvm_info(get_full_name(), $sformatf("%0s is generated", test_name), UVM_LOW)
  endfunction

  // Helper function to generate the proper sequence of handshake instructions
  // to signal the testbench (see riscv_signature_pkg.sv)
  function void gen_signature_handshake(ref string instr[$],
                                        input signature_type_t signature_type,
                                        core_status_t core_status = INITIALIZED,
                                        test_result_t test_result = TEST_FAIL,
                                        privileged_reg_t csr = MSCRATCH,
                                        string addr_label = "");
    if (cfg.require_signature_addr) begin
      string str[$];
      str = {$sformatf("li x%0d, 0x%0h", cfg.signature_addr_reg, cfg.signature_addr)};
      instr = {instr, str};
      case (signature_type)
        // A single data word is written to the signature address.
        // Bits [7:0] contain the signature_type of CORE_STATUS, and the upper
        // XLEN-8 bits contain the core_status_t data.
        CORE_STATUS: begin
          str = {$sformatf("li x%0d, 0x%0h", cfg.signature_data_reg, core_status),
                 $sformatf("slli x%0d, x%0d, 8", cfg.signature_data_reg, cfg.signature_data_reg),
                 $sformatf("addi x%0d, x%0d, 0x%0h", cfg.signature_data_reg,
                           cfg.signature_data_reg, signature_type),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.signature_data_reg, cfg.signature_addr_reg)};
          instr = {instr, str};
        end
        // A single data word is written to the signature address.
        // Bits [7:0] contain the signature_type of TEST_RESULT, and the upper
        // XLEN-8 bits contain the test_result_t data.
        TEST_RESULT: begin
          str = {$sformatf("li x%0d, 0x%0h", cfg.signature_data_reg, test_result),
                 $sformatf("slli x%0d, x%0d, 8", cfg.signature_data_reg, cfg.signature_data_reg),
                 $sformatf("addi x%0d, x%0d, 0x%0h", cfg.signature_data_reg,
                           cfg.signature_data_reg, signature_type),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.signature_data_reg, cfg.signature_addr_reg)};
          instr = {instr, str};
        end
        // The first write to the signature address contains just the
        // signature_type of WRITE_GPR.
        // It is followed by 32 consecutive writes to the signature address,
        // each writing the data contained in one GPR, starting from x0 as the
        // first write, and ending with x31 as the 32nd write.
        WRITE_GPR: begin
          str = {$sformatf("li x%0d, 0x%0h", cfg.signature_data_reg, signature_type),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.signature_data_reg, cfg.signature_addr_reg)};
          instr = {instr, str};
          for(int i = 0; i < 32; i++) begin
            str = {$sformatf("sw x%0x, 0(x%0d)", i, cfg.signature_addr_reg)};
            instr = {instr, str};
          end
        end
        // The first write to the signature address contains the
        // signature_type of WRITE_CSR in bits [7:0], and the CSR address in
        // the upper XLEN-8 bits.
        // It is followed by a second write to the signature address,
        // containing the data stored in the specified CSR.
        WRITE_CSR: begin
          str = {$sformatf("li x%0d, 0x%0h", cfg.signature_data_reg, csr),
                 $sformatf("slli x%0d, x%0d, 8", cfg.signature_data_reg, cfg.signature_data_reg),
                 $sformatf("addi x%0d, x%0d, 0x%0h", cfg.signature_data_reg,
                           cfg.signature_data_reg, signature_type),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.signature_data_reg, cfg.signature_addr_reg),
                 $sformatf("csrr x%0d, 0x%0h", cfg.signature_data_reg, csr),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.signature_data_reg, cfg.signature_addr_reg)};
          instr = {instr, str};
        end
        default: begin
          `uvm_fatal(`gfn, "signature_type is not defined")
        end
      endcase
    end
 endfunction

  //---------------------------------------------------------------------------------------
  // Inject directed instruction stream
  //---------------------------------------------------------------------------------------

  virtual function void add_directed_instr_stream(string name, int unsigned ratio);
    directed_instr_stream_ratio[name] = ratio;
    `uvm_info(`gfn, $sformatf("Adding directed instruction stream:%0s ratio:%0d/1000", name, ratio), UVM_LOW)
  endfunction

  virtual function void get_directed_instr_stream();
    string args, val;
    string opts[$];
    for (int i=0; i<cfg.max_directed_instr_stream_seq; i++) begin
      args = $sformatf("directed_instr_%0d=", i);
      if ($value$plusargs({args,"%0s"}, val)) begin
        uvm_split_string(val, ",", opts);
        if (opts.size() != 2) begin
          `uvm_fatal(`gfn, $sformatf(
            "Incorrect directed instruction format : %0s, expect: name,ratio", val))
        end else begin
          add_directed_instr_stream(opts[0], opts[1].atoi());
        end
      end
    end
  endfunction

  // Generate directed instruction stream based on the ratio setting
  virtual function void generate_directed_instr_stream(input string label,
                                                       input int unsigned original_instr_cnt,
                                                       input int unsigned min_insert_cnt = 0,
                                                       input bit kernel_mode = 0,
                                                       output riscv_instr_stream instr_stream[]);
    uvm_object object_h;
    riscv_rand_instr_stream new_instr_stream;
    int unsigned instr_insert_cnt;
    int unsigned idx;
    uvm_coreservice_t coreservice = uvm_coreservice_t::get();
    uvm_factory factory = coreservice.get_factory();
    if(cfg.no_directed_instr) return;
    foreach(directed_instr_stream_ratio[instr_stream_name]) begin
      instr_insert_cnt = original_instr_cnt * directed_instr_stream_ratio[instr_stream_name] / 1000;
      if(instr_insert_cnt <= min_insert_cnt) begin
        instr_insert_cnt = min_insert_cnt;
      end
      `ifdef DSIM
        // Temporarily skip loop instruction for dsim as it cannot support dynamic array
        // randomization
        if (uvm_is_match("*loop*", instr_stream_name)) begin
          `uvm_info(`gfn, $sformatf("%0s is skipped", instr_stream_name), UVM_LOW)
          continue;
        end
      `endif
      `uvm_info(get_full_name(), $sformatf("Insert directed instr stream %0s %0d/%0d times",
                                 instr_stream_name, instr_insert_cnt, original_instr_cnt), UVM_LOW)
      for(int i = 0; i < instr_insert_cnt; i++) begin
        string name = $sformatf("%0s_%0d", instr_stream_name, i);
        object_h = factory.create_object_by_name(instr_stream_name, get_full_name(), name);
        if(object_h == null) begin
          `uvm_fatal(get_full_name(), $sformatf("Cannot create instr stream %0s", name))
        end
        if($cast(new_instr_stream, object_h)) begin
          new_instr_stream.cfg = cfg;
          new_instr_stream.label = $sformatf("%0s_instr_%0d", label, idx);
          new_instr_stream.kernel_mode = kernel_mode;
          `DV_CHECK_RANDOMIZE_FATAL(new_instr_stream)
          instr_stream = {instr_stream, new_instr_stream};
        end else begin
          `uvm_fatal(get_full_name(), $sformatf("Cannot cast instr stream %0s", name))
        end
        idx++;
      end
    end
    instr_stream.shuffle();
  endfunction

  //---------------------------------------------------------------------------------------
  // Generate the debug rom, and any related programs
  //---------------------------------------------------------------------------------------

  // Generate the program in the debug ROM
  // Processor will fetch instruction from here upon receiving debug request from debug module
  virtual function void gen_debug_rom();
    string instr[$];
    string debug_end[$];
    string dret;
    string debug_sub_program_name[$] = {};
    string str[$];
    if (riscv_instr_pkg::support_debug_mode) begin
      dret = {format_string(" ", LABEL_STR_LEN), "dret"};
      // The main debug rom
      if (!cfg.gen_debug_section) begin
        // If the debug section should not be generated, we just populate it
        // with a dret instruction.
        instr = {dret};
        gen_section("debug_rom", instr);
      end else begin
        if (cfg.enable_ebreak_in_debug_rom) begin
          // As execution of ebreak in D mode causes core to
          // re-enter D mode, this directed sequence will be a loop that ensures the
          // ebreak instruction will only be executed once to prevent infinitely
          // looping back to the beginning of the debug rom.
          // Write dscratch to random GPR and branch to debug_end if greater
          // than 0, for ebreak loops.
          // Use dscratch1 to store original GPR value.
          str = {$sformatf("csrw 0x%0x, x%0d", DSCRATCH1, cfg.scratch_reg),
                 $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0)};
          instr = {instr, str};
          // send dpc and dcsr to testbench, as this handshake will be
          // executed twice due to the ebreak loop, there should be no change
          // in their values as by the Debug Mode Spec Ch. 4.1.8
          gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(DCSR));
          gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(DPC));
          str = {$sformatf("beq x%0d, x0, 1f", cfg.scratch_reg),
                 $sformatf("j debug_end"),
                 $sformatf("1: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)};
          instr = {instr, str};
        end
        // Need to save off GPRs to avoid modifying program flow
        push_gpr_to_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, instr);
        // Signal that the core entered debug rom only if the rom is actually
        // being filled with random instructions to prevent stress tests from
        // having to execute unnecessary push/pop of GPRs on the stack ever
        // time a debug request is sent
        gen_signature_handshake(instr, CORE_STATUS, IN_DEBUG_MODE);
        if (cfg.set_dcsr_ebreak) begin
          // We want to set dcsr.ebreak(m/s/u) to 1'b1, depending on what modes
          // are available.
          // TODO(udinator) - randomize the dcsr.ebreak setup
          gen_dcsr_ebreak(instr);
        end
        // Check dcsr.cause, and update dpc by 0x4 if the cause is ebreak, as
        // ebreak will set set dpc to its own address, which will cause an
        // infinite loop.
        str = {$sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
               $sformatf("slli x%0d, x%0d, 0x17", cfg.scratch_reg, cfg.scratch_reg),
               $sformatf("srli x%0d, x%0d, 0x1d", cfg.scratch_reg, cfg.scratch_reg),
               $sformatf("li x%0d, 0x1", cfg.signature_data_reg),
               $sformatf("bne x%0d, x%0d, 2f", cfg.scratch_reg, cfg.signature_data_reg)};
        instr = {instr, str};
        increment_csr(DPC, 4, instr);
        str = {"2: nop"};
        instr = {instr, str};
        // write DCSR to the testbench for any analysis
        gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(DCSR));
        // Increment dscratch0 by 1 to update the loop counter for all ebreak
        // tests
        if (cfg.enable_ebreak_in_debug_rom || cfg.set_dcsr_ebreak) begin
          // Add 1 to dscratch0
          increment_csr(DSCRATCH0, 1, instr);
          str = {$sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)};
          instr = {instr, str};
        end
        format_section(instr);
        gen_sub_program(debug_sub_program, debug_sub_program_name,
                        cfg.num_debug_sub_program, 1'b1, "debug_sub");
        debug_program = riscv_instr_sequence::type_id::create("debug_program");
        debug_program.instr_cnt = cfg.debug_program_instr_cnt;
        debug_program.is_debug_program = 1;
        debug_program.cfg = cfg;
        `DV_CHECK_RANDOMIZE_FATAL(debug_program)
        debug_program.gen_instr(.is_main_program(1'b1), .no_branch(1'b0));
        gen_callstack(debug_program, debug_sub_program, debug_sub_program_name,
                      cfg.num_debug_sub_program);
        debug_program.post_process_instr();
        debug_program.generate_instr_stream(.no_label(1'b1));
        insert_sub_program(debug_sub_program, instr_stream);
        instr = {instr, debug_program.instr_string_list};
        gen_section("debug_rom", instr);
        // Set dscratch0 back to 0x0 to prepare for the next entry into debug
        // mode, and write dscratch0 and dcsr to the testbench for any
        // analysis
        if (cfg.enable_ebreak_in_debug_rom) begin
          str = {$sformatf("csrwi 0x%0x, 0x0", DSCRATCH0)};
          debug_end = {debug_end, str};
        end
        pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, debug_end);
        // We have been using dscratch1 to store the
        // value of our given scratch register for use in ebreak loop, so we
        // need to restore its value before returning from D mode
        if (cfg.enable_ebreak_in_debug_rom) begin
          str = {$sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)};
          debug_end = {debug_end, str};
        end
        format_section(debug_end);
        debug_end = {debug_end, dret};
        gen_section("debug_end", debug_end);
      end
    end
  endfunction

  // Generate exception handling routine for debug ROM
  virtual function void gen_debug_exception_handler();
    if (riscv_instr_pkg::support_debug_mode) begin
      string instr[];
      instr = {"dret"};
      gen_section("debug_exception", instr);
    end
  endfunction

  // Set dcsr.ebreak(m/s/u)
  // TODO(udinator) - randomize the setup for these fields
  virtual function void gen_dcsr_ebreak(ref string instr[$]);
    string str;
    if (MACHINE_MODE inside {riscv_instr_pkg::supported_privileged_mode}) begin
      str = $sformatf("li x%0d, 0x8000", cfg.scratch_reg);
      instr.push_back(str);
      str = $sformatf("csrs dcsr, x%0d", cfg.scratch_reg);
      instr.push_back(str);
    end
    if (SUPERVISOR_MODE inside {riscv_instr_pkg::supported_privileged_mode}) begin
      str = $sformatf("li x%0d, 0x2000", cfg.scratch_reg);
      instr.push_back(str);
      str = $sformatf("csrs dcsr, x%0d", cfg.scratch_reg);
      instr.push_back(str);
    end
    if (USER_MODE inside {riscv_instr_pkg::supported_privileged_mode}) begin
      str = $sformatf("li x%0d, 0x1000", cfg.scratch_reg);
      instr.push_back(str);
      str = $sformatf("csrs dcsr, x%0d", cfg.scratch_reg);
      instr.push_back(str);
    end
  endfunction

  virtual function void increment_csr(privileged_reg_t csr, int val, ref string instr[$]);
    string str;
    str = $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, csr);
    instr.push_back(str);
    str = $sformatf("addi x%0d, x%0d, 0x%0x", cfg.scratch_reg, cfg.scratch_reg, val);
    instr.push_back(str);
    str = $sformatf("csrw 0x%0x, x%0d", csr, cfg.scratch_reg);
    instr.push_back(str);
  endfunction

endclass
