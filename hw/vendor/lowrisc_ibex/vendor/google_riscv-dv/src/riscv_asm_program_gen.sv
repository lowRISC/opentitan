/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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
   riscv_instr_sequence                main_program[NUM_HARTS];
   riscv_instr_sequence                sub_program[NUM_HARTS][];
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
   riscv_instr_stream                  directed_instr[];
   string                              instr_stream[$];
   riscv_callstack_gen                 callstack_gen;
   riscv_privileged_common_seq         privil_seq;
   // Directed instruction ratio, occurance per 1000 instructions
   int unsigned                        directed_instr_stream_ratio[string];
   riscv_page_table_list#(SATP_MODE)   page_table_list;
   int                                 hart;

  `uvm_object_utils(riscv_asm_program_gen)

  function new (string name = "");
    super.new(name);
  endfunction

  //---------------------------------------------------------------------------------------
  // Main function to generate the whole program
  //---------------------------------------------------------------------------------------

  // This is the main function to generate all sections of the program.
  virtual function void gen_program();
    instr_stream.delete();
    // Generate program header
    gen_program_header();
    for (int hart = 0; hart < cfg.num_of_harts; hart++) begin
      string sub_program_name[$];
      instr_stream.push_back($sformatf("h%0d_start:", hart));
      if (!cfg.bare_program_mode) begin
        setup_misa();
        // Create all page tables
        create_page_table(hart);
        // Setup privileged mode registers and enter target privileged mode
        pre_enter_privileged_mode(hart);
      end
      // Init section
      gen_init_section(hart);
      // If PMP is supported, we want to generate the associated trap handlers and the test_done
      // section at the start of the program so we can allow access through the pmpcfg0 CSR
      if (riscv_instr_pkg::support_pmp && !cfg.bare_program_mode) begin
        gen_trap_handlers(hart);
        // Ecall handler
        gen_ecall_handler(hart);
        // Instruction fault handler
        gen_instr_fault_handler(hart);
        // Load fault handler
        gen_load_fault_handler(hart);
        // Store fault handler
        gen_store_fault_handler(hart);
        if (hart == 0) begin
          gen_test_done();
        end
      end
      // Generate sub program
      gen_sub_program(hart, sub_program[hart], sub_program_name, cfg.num_of_sub_program);
      // Generate main program
      main_program[hart] = riscv_instr_sequence::type_id::create(get_label("main", hart));
      main_program[hart].instr_cnt = cfg.main_program_instr_cnt;
      main_program[hart].is_debug_program = 0;
      main_program[hart].label_name = main_program[hart].get_name();
      generate_directed_instr_stream(.hart(hart),
                                     .label(main_program[hart].label_name),
                                     .original_instr_cnt(main_program[hart].instr_cnt),
                                     .min_insert_cnt(1),
                                     .instr_stream(main_program[hart].directed_instr));
      main_program[hart].cfg = cfg;
      `DV_CHECK_RANDOMIZE_FATAL(main_program[hart])
      main_program[hart].gen_instr(.is_main_program(1), .no_branch(cfg.no_branch_jump));
      // Setup jump instruction among main program and sub programs
      gen_callstack(main_program[hart], sub_program[hart], sub_program_name,
                    cfg.num_of_sub_program);
      `uvm_info(`gfn, "Generating callstack...done", UVM_LOW)
      main_program[hart].post_process_instr();
      `uvm_info(`gfn, "Post-processing main program...done", UVM_LOW)
      main_program[hart].generate_instr_stream();
      `uvm_info(`gfn, "Generating main program instruction stream...done", UVM_LOW)
      instr_stream = {instr_stream, main_program[hart].instr_string_list};
      // If PMP is supported, need to jump from end of main program to test_done section at the end
      // of main_program, as the test_done will have moved to the beginning of the program
      instr_stream = {instr_stream,
                      $sformatf("%sla x%0d, test_done", indent, cfg.scratch_reg),
                      $sformatf("%sjalr x0, x%0d, 0", indent, cfg.scratch_reg)
                     };
      // Test done section
      // If PMP isn't supported, generate this in the normal location
      if (hart == 0 & !riscv_instr_pkg::support_pmp) begin
        gen_test_done();
      end
      // Shuffle the sub programs and insert to the instruction stream
      insert_sub_program(sub_program[hart], instr_stream);
      `uvm_info(`gfn, "Inserting sub-programs...done", UVM_LOW)
      `uvm_info(`gfn, "Main/sub program generation...done", UVM_LOW)
      // Program end
      gen_program_end(hart);
      if (!cfg.bare_program_mode) begin
        // Generate debug rom section
        if (riscv_instr_pkg::support_debug_mode) begin
          gen_debug_rom(hart);
        end
      end
      gen_section({hart_prefix(hart), "instr_end"}, {"nop"});
    end
    for (int hart = 0; hart < cfg.num_of_harts; hart++) begin
      // Starting point of data section
      gen_data_page_begin(hart);
      if(!cfg.no_data_page) begin
        // User data section
        gen_data_page(hart);
        // AMO memory region
        if ((hart == 0) && (RV32A inside {supported_isa})) begin
          gen_data_page(hart, .amo(1));
        end
      end
      // Stack section
      gen_stack_section(hart);
      if (!cfg.bare_program_mode) begin
        // Generate kernel program/data/stack section
        gen_kernel_sections(hart);
      end
      // Page table
      if (!cfg.bare_program_mode) begin
        gen_page_table_section(hart);
      end
    end
  endfunction

  //---------------------------------------------------------------------------------------
  // Generate kernel program/data/stack sections
  //---------------------------------------------------------------------------------------
  virtual function void gen_kernel_sections(int hart);
    if (SATP_MODE != BARE) begin
      instr_stream.push_back(".align 12");
    end else begin
      instr_stream.push_back(".align 2");
    end
    instr_stream.push_back(get_label("kernel_instr_start:", hart));
    instr_stream.push_back(".text");
    // Kernel programs
    if (cfg.virtual_addr_translation_on) begin
      umode_program = riscv_instr_sequence::type_id::create(get_label("umode_program", hart));
      gen_kernel_program(hart, umode_program);
      smode_program = riscv_instr_sequence::type_id::create(get_label("smode_program", hart));
      gen_kernel_program(hart, smode_program);
      smode_lsu_program = riscv_instr_sequence::type_id::create(
                          get_label("smode_lsu_program", hart));
      gen_kernel_program(hart, smode_lsu_program);
    end
    // All trap/interrupt handling is in the kernel region
    // Trap/interrupt delegation to user mode is not supported now
    // Trap handler
    gen_all_trap_handler(hart);
    // Interrupt handling subroutine
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      gen_interrupt_handler_section(riscv_instr_pkg::supported_privileged_mode[i], hart);
    end
    instr_stream.push_back(get_label("kernel_instr_end: nop", hart));
    // User stack and data pages may not be accessible when executing trap handling programs in
    // machine/supervisor mode. Generate separate kernel data/stack sections to solve it.
    if (cfg.virtual_addr_translation_on) begin
      if (SATP_MODE != BARE) begin
        instr_stream.push_back(".align 12");
      end else begin
        instr_stream.push_back(".align 2");
      end
      // Kernel data pages
      instr_stream.push_back(get_label("kernel_data_start:", hart));
      if(!cfg.no_data_page) begin
        // Data section
        gen_data_page(hart, 1'b1);
      end
    end
    // Kernel stack section
    gen_kernel_stack_section(hart);
  endfunction

  virtual function void gen_kernel_program(int hart, riscv_instr_sequence seq);
    seq.instr_cnt = cfg.kernel_program_instr_cnt;
    generate_directed_instr_stream(.hart(hart),
                                   .label(seq.get_name()),
                                   .original_instr_cnt(seq.instr_cnt),
                                   .min_insert_cnt(0),
                                   .instr_stream(seq.directed_instr),
                                   .kernel_mode(1'b1));
    seq.label_name = seq.get_name();
    seq.is_debug_program = 0;
    seq.cfg = cfg;
    `DV_CHECK_RANDOMIZE_FATAL(seq)
    seq.gen_instr(.is_main_program(0), .no_branch(cfg.no_branch_jump));
    seq.post_process_instr();
    seq.generate_instr_stream();
    instr_stream = {instr_stream, seq.instr_string_list};
  endfunction

  //---------------------------------------------------------------------------------------
  // Generate any subprograms and set up the callstack
  //---------------------------------------------------------------------------------------

  virtual function void gen_sub_program(int hart,
                                        ref riscv_instr_sequence sub_program[],
                                        ref string sub_program_name[$],
                                        input int num_sub_program,
                                        bit is_debug = 1'b0,
                                        string prefix = "sub");
    if(num_sub_program > 0) begin
      sub_program = new[num_sub_program];
      foreach(sub_program[i]) begin
        sub_program[i] = riscv_instr_sequence::type_id::create(
                         get_label($sformatf("%s_%0d", prefix, i + 1), hart));
        `uvm_info(`gfn, $sformatf("sub program name: %s", sub_program[i].get_name()), UVM_LOW)
        sub_program[i].is_debug_program = is_debug;
        if (is_debug) begin
          sub_program[i].instr_cnt = cfg.debug_sub_program_instr_cnt[i];
        end else begin
          sub_program[i].instr_cnt = cfg.sub_program_instr_cnt[i];
        end
        generate_directed_instr_stream(.hart(hart),
                                       .label(sub_program[i].get_name()),
                                       .original_instr_cnt(sub_program[i].instr_cnt),
                                       .min_insert_cnt(0),
                                       .instr_stream(sub_program[i].directed_instr));
        sub_program[i].label_name = sub_program[i].get_name();
        sub_program[i].cfg = cfg;
        `DV_CHECK_RANDOMIZE_FATAL(sub_program[i])
        sub_program[i].gen_instr(.is_main_program(0), .no_branch(cfg.no_branch_jump));
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
    string str[$];
    instr_stream.push_back(".include \"user_define.h\"");
    instr_stream.push_back(".globl _start");
    instr_stream.push_back(".section .text");
    if (cfg.disable_compressed_instr) begin
      instr_stream.push_back(".option norvc;");
    end
    str.push_back(".include \"user_init.s\"");
    str.push_back($sformatf("csrr x5, 0x%0x", MHARTID));
    for (int hart = 0; hart < cfg.num_of_harts; hart++) begin
      str = {str, $sformatf("li x6, %0d", hart),
                  $sformatf("beq x5, x6, %0df", hart)};
    end
    gen_section("_start", str);
    for (int hart = 0; hart < cfg.num_of_harts; hart++) begin
      instr_stream.push_back($sformatf("%0d: la x%0d, h%0d_start", hart, cfg.scratch_reg, hart));
      instr_stream.push_back($sformatf("jalr x0, x%0d, 0", cfg.scratch_reg));
    end
  endfunction

  virtual function void gen_program_end(int hart);
    if (hart == 0) begin
      // Use write_tohost to terminate spike simulation
      gen_section("write_tohost", {"sw gp, tohost, t5"});
      gen_section("_exit", {"j write_tohost"});
    end
  endfunction

  virtual function void gen_data_page_begin(int hart);
    instr_stream.push_back(".section .data");
    if (hart == 0) begin
      instr_stream.push_back(".align 6; .global tohost; tohost: .dword 0;");
      instr_stream.push_back(".align 6; .global fromhost; fromhost: .dword 0;");
    end
  endfunction

  virtual function void gen_data_page(int hart, bit is_kernel = 1'b0, bit amo = 0);
    string data_page;
    data_page_gen = riscv_data_page_gen::type_id::create("data_page_gen");
    data_page_gen.cfg = cfg;
    data_page_gen.gen_data_page(hart, cfg.data_page_pattern, is_kernel, amo);
    instr_stream = {instr_stream, data_page_gen.data_page_str};
  endfunction

  // Generate the user stack section
  virtual function void gen_stack_section(int hart);
    string hart_prefix_string = hart_prefix(hart);
    if (cfg.use_push_data_section) begin
      instr_stream.push_back($sformatf(".pushsection .%0suser_stack,\"aw\",@progbits;",
                             hart_prefix_string));
    end else begin
      instr_stream.push_back($sformatf(".section .%0suser_stack,\"aw\",@progbits;",
                             hart_prefix_string));
    end
    if (SATP_MODE != BARE) begin
      instr_stream.push_back(".align 12");
    end else begin
      instr_stream.push_back(".align 2");
    end
    instr_stream.push_back(get_label("user_stack_start:", hart));
    instr_stream.push_back($sformatf(".rept %0d", cfg.stack_len - 1));
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    instr_stream.push_back(".endr");
    instr_stream.push_back(get_label("user_stack_end:", hart));
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    if (cfg.use_push_data_section) begin
      instr_stream.push_back(".popsection;");
    end
  endfunction

  // The kernal stack is used to save user program context before executing exception handling
  virtual function void gen_kernel_stack_section(int hart);
    string hart_prefix_string = hart_prefix(hart);
    if (cfg.use_push_data_section) begin
      instr_stream.push_back($sformatf(".pushsection .%0skernel_stack,\"aw\",@progbits;",
                             hart_prefix_string));
    end else begin
      instr_stream.push_back($sformatf(".section .%0skernel_stack,\"aw\",@progbits;",
                             hart_prefix_string));
    end
    if (SATP_MODE != BARE) begin
      instr_stream.push_back(".align 12");
    end else begin
      instr_stream.push_back(".align 2");
    end
    instr_stream.push_back(get_label("kernel_stack_start:", hart));
    instr_stream.push_back($sformatf(".rept %0d", cfg.kernel_stack_len - 1));
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    instr_stream.push_back(".endr");
    instr_stream.push_back(get_label("kernel_stack_end:", hart));
    instr_stream.push_back($sformatf(".%0dbyte 0x0", XLEN/8));
    if (cfg.use_push_data_section) begin
      instr_stream.push_back(".popsection;");
    end
  endfunction

  virtual function void gen_init_section(int hart);
    string str;
    str = format_string(get_label("init:", hart), LABEL_STR_LEN);
    instr_stream.push_back(str);
    if (cfg.enable_floating_point) begin
      init_floating_point_gpr();
    end
    init_gpr();
    // Init stack pointer to point to the end of the user stack
    str = {indent, $sformatf("la x%0d, %0suser_stack_end", cfg.sp, hart_prefix(hart))};
    instr_stream.push_back(str);
    if (cfg.enable_vector_extension) begin
      randomize_vec_gpr_and_csr();
    end
    core_is_initialized();
    gen_dummy_csr_write(); // TODO add a way to disable xStatus read
    if (riscv_instr_pkg::support_pmp) begin
      str = {indent, "j main"};
      instr_stream.push_back(str);
    end
  endfunction

  // Setup MISA based on supported extensions
  virtual function void setup_misa();
    bit [XLEN-1:0] misa;
    misa[XLEN-1:XLEN-2] = (XLEN == 32) ? 2'b01 :
                          (XLEN == 64) ? 2'b10 : 2'b11;
    if (cfg.check_misa_init_val) begin
      instr_stream.push_back({indent, $sformatf("csrr x15, 0x%0x", MISA)});
    end
    foreach (supported_isa[i]) begin
      case (supported_isa[i]) inside
        RV32C, RV64C, RV128C : misa[MISA_EXT_C] = 1'b1;
        RV32I, RV64I, RV128I : misa[MISA_EXT_I] = 1'b1;
        RV32M, RV64M         : misa[MISA_EXT_M] = 1'b1;
        RV32A, RV64A         : misa[MISA_EXT_A] = 1'b1;
        RV32B, RV64B         : misa[MISA_EXT_B] = 1'b1;
        RV32F, RV64F, RV32FC : misa[MISA_EXT_F] = 1'b1;
        RV32D, RV64D, RV32DC : misa[MISA_EXT_D] = 1'b1;
        RVV                  : misa[MISA_EXT_V] = 1'b1;
        RV32X, RV64X         : misa[MISA_EXT_X] = 1'b1;
        default : `uvm_fatal(`gfn, $sformatf("%0s is not yet supported",
                                   supported_isa[i].name()))
      endcase
    end
    if (SUPERVISOR_MODE inside {supported_privileged_mode}) begin
      misa[MISA_EXT_S] = 1'b1;
    end
    instr_stream.push_back({indent, $sformatf("li x%0d, 0x%0x", cfg.gpr[0], misa)});
    instr_stream.push_back({indent, $sformatf("csrw 0x%0x, x%0d", MISA, cfg.gpr[0])});
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

  // Generate some dummy writes to xSTATUS/xIE at the beginning of the test to check
  // repeated writes to these CSRs.
  virtual function void gen_dummy_csr_write();
    string instr[$];
    if (cfg.enable_dummy_csr_write) begin
      case (cfg.init_privileged_mode)
        MACHINE_MODE: begin
          instr.push_back($sformatf("csrr x%0d, 0x%0x", cfg.gpr[0], MSTATUS));
          instr.push_back($sformatf("csrr x%0d, 0x%0x", cfg.gpr[1], MIE));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", MSTATUS, cfg.gpr[0]));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", MIE, cfg.gpr[1]));
        end
        SUPERVISOR_MODE: begin
          instr.push_back($sformatf("csrr x%0d, 0x%0x", cfg.gpr[0], SSTATUS));
          instr.push_back($sformatf("csrr x%0d, 0x%0x", cfg.gpr[1], SIE));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", SSTATUS, cfg.gpr[0]));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", SIE, cfg.gpr[1]));
        end
        USER_MODE: begin
          if (!riscv_instr_pkg::support_umode_trap) begin
            return;
          end
          instr.push_back($sformatf("csrr x%0d, 0x%0x", cfg.gpr[0], USTATUS));
          instr.push_back($sformatf("csrr x%0d, 0x%0x", cfg.gpr[1], UIE));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", USTATUS, cfg.gpr[0]));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", UIE, cfg.gpr[1]));
        end
        default: begin
          `uvm_fatal(`gfn, "Unsupported boot mode")
        end
      endcase
      format_section(instr);
      instr_stream = {instr_stream, instr};
    end
  endfunction

  // Initialize general purpose registers with random value
  virtual function void init_gpr();
    string str;
    bit [DATA_WIDTH-1:0] reg_val;
    // Init general purpose registers with random values
    for(int i = 0; i < NUM_GPR; i++) begin
      if (i inside {cfg.sp, cfg.tp}) continue;
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

  // Initialize vector general purpose registers
  virtual function void init_vec_gpr();
    int SEW;
    int LMUL;
    int EDIV = 1;
    int len = (ELEN <= XLEN) ? ELEN : XLEN;
    int num_elements = VLEN / len;
    if (!(RVV inside {supported_isa})) return;
    LMUL = 1;
    SEW = (ELEN <= XLEN) ? ELEN : XLEN;
    instr_stream.push_back($sformatf("li x%0d, %0d", cfg.gpr[1], cfg.vector_cfg.vl));
    instr_stream.push_back($sformatf("%svsetvli x%0d, x%0d, e%0d, m%0d, d%0d",
                                     indent, cfg.gpr[0], cfg.gpr[1], SEW, LMUL, EDIV));
    instr_stream.push_back("vec_reg_init:");

    // Vector registers will be initialized using one of the following three methods
    case (cfg.vreg_init_method)
      SAME_VALUES_ALL_ELEMS: begin
        for (int v = 0; v < NUM_VEC_GPR; v++) begin
          instr_stream.push_back($sformatf("%0svmv.v.x v%0d, x%0d", indent, v, v));
        end
      end
      RANDOM_VALUES_VMV: begin
        for (int v = 0; v < NUM_VEC_GPR; v++) begin
          for (int e = 0; e < num_elements; e++) begin
            if (e > 0) instr_stream.push_back($sformatf("%0svmv.v.v v0, v%0d", indent, v));
            instr_stream.push_back($sformatf("%0sli x%0d, 0x%0x",
                                             indent, cfg.gpr[0], $urandom_range(0, 2 ** SEW - 1)));
            if (v > 0) begin
              instr_stream.push_back($sformatf("%0svslide1up.vx v%0d, v0, x%0d",
                                               indent, v, cfg.gpr[0]));
            end else begin
              instr_stream.push_back($sformatf("%0svslide1up.vx v%0d, v1, x%0d",
                                               indent, v, cfg.gpr[0]));
            end
          end
        end
      end
      RANDOM_VALUES_LOAD: begin
        // Select those memory regions that are big enough for load a vreg
        mem_region_t valid_mem_region [$];
        foreach (cfg.mem_region[i])
          if (cfg.mem_region[i].size_in_bytes * 8 >= VLEN) valid_mem_region.push_back(cfg.mem_region[i]);

        if (valid_mem_region.size() == 0)
          `uvm_fatal(`gfn, "Couldn't find a memory region big enough to initialize the vector registers")

        for (int v = 0; v < NUM_VEC_GPR; v++) begin
          int region = $urandom_range(0, valid_mem_region.size()-1);
          instr_stream.push_back($sformatf("%0sla t0, %0s", indent, valid_mem_region[region].name));
          instr_stream.push_back($sformatf("%0svle.v v%0d, (t0)", indent, v));
        end
      end
    endcase
  endfunction

  // Initialize floating point general purpose registers
  virtual function void init_floating_point_gpr();
    int int_gpr;
    string str;
    for(int i = 0; i < NUM_FLOAT_GPR; i++) begin
      randcase
        1: init_floating_point_gpr_with_spf(i);
        RV64D inside {supported_isa}: init_floating_point_gpr_with_dpf(i);
      endcase
    end
    // Initialize rounding mode of FCSR
    str = $sformatf("%0sfsrmi %0d", indent, cfg.fcsr_rm);
    instr_stream.push_back(str);
  endfunction

  // get instructions initialize floating_point_gpr with single precision floating value
  virtual function void init_floating_point_gpr_with_spf(int int_floating_gpr);
    string str;
    bit [31:0] imm = get_rand_spf_value();
    str = $sformatf("%0sli x%0d, %0d", indent, cfg.gpr[0], imm);
    instr_stream.push_back(str);
    str = $sformatf("%0sfmv.w.x f%0d, x%0d", indent, int_floating_gpr, cfg.gpr[0]);
    instr_stream.push_back(str);
  endfunction

  // get instructions initialize floating_point_gpr with double precision floating value
  virtual function void init_floating_point_gpr_with_dpf(int int_floating_gpr);
    string str;
    bit [63:0] imm = get_rand_dpf_value();
    int int_gpr1 = cfg.gpr[0];
    int int_gpr2 = cfg.gpr[1];

    str = $sformatf("%0sli x%0d, %0d", indent, int_gpr1, imm[63:32]);
    instr_stream.push_back(str);
    // shift to upper 32bits
    repeat (2) begin
      str = $sformatf("%0sslli x%0d, x%0d, 16", indent, int_gpr1, int_gpr1);
      instr_stream.push_back(str);
    end
    str = $sformatf("%0sli x%0d, %0d", indent, int_gpr2, imm[31:0]);
    instr_stream.push_back(str);
    str = $sformatf("%0sor x%0d, x%0d, x%0d", indent, int_gpr2, int_gpr2, int_gpr1);
    instr_stream.push_back(str);
    str = $sformatf("%0sfmv.d.x f%0d, x%0d", indent, int_floating_gpr, int_gpr2);
    instr_stream.push_back(str);
  endfunction

  // get a random single precision floating value
  virtual function bit [XLEN-1:0] get_rand_spf_value();
    bit [31:0] value;

    randcase
      // infinity
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
                                            value inside {32'h7f80_0000, 32'hff80_0000};)
      // largest
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
                                            value inside {32'h7f7f_ffff, 32'hff7f_ffff};)
      // zero
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
                                            value inside {32'h0000_0000, 32'h8000_0000};)
      // NaN
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
                                            value inside {32'h7f80_0001, 32'h7fc0_0000};)
      // normal
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
                                            value[30:SINGLE_PRECISION_FRACTION_BITS] > 0;)
      // subnormal
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
                                            value[30:SINGLE_PRECISION_FRACTION_BITS] == 0;)
    endcase
    return value;
  endfunction

  // get a random double precision floating value
  virtual function bit [XLEN-1:0] get_rand_dpf_value();
    bit [63:0] value;

    randcase
      // infinity
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value inside {64'h7ff0_0000_0000_0000, 64'hfff0_0000_0000_0000};)
      // largest
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value inside {64'h7fef_ffff_ffff_ffff, 64'hffef_ffff_ffff_ffff};)
      // zero
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value inside {64'h0000_0000_0000_0000, 64'h8000_0000_0000_0000};)
      // NaN
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value inside {64'h7ff0_0000_0000_0001, 64'h7ff8_0000_0000_0000};)
      // normal
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value[62:DOUBLE_PRECISION_FRACTION_BITS] > 0;)
      // subnormal
      1: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value[62:DOUBLE_PRECISION_FRACTION_BITS] == 0;)
    endcase
    return value;
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
  virtual function void gen_register_dump(ref string instr[$]);
    string str;
    // Load base address
    str = $sformatf("la x%0d, _start", cfg.gpr[0]);
    instr.push_back(str);
    // Generate sw/sd instructions
    for(int i = 0; i < 32; i++) begin
      if(XLEN == 64) begin
        str = $sformatf("sd x%0d, %0d(x%0d)", i, i*(XLEN/8), cfg.gpr[0]);
      end else begin
        str = $sformatf("sw x%0d, %0d(x%0d)", i, i*(XLEN/8), cfg.gpr[0]);
      end
      instr.push_back(str);
    end
  endfunction

  //---------------------------------------------------------------------------------------
  // Privileged mode entering routine
  //---------------------------------------------------------------------------------------

  virtual function void pre_enter_privileged_mode(int hart);
    string instr[];
    string str[$];
    // Setup kerenal stack pointer
    str = {$sformatf("la x%0d, %0skernel_stack_end", cfg.tp, hart_prefix(hart))};
    gen_section(get_label("kernel_sp", hart), str);
    // Setup interrupt and exception delegation
    if(!cfg.no_delegation && (cfg.init_privileged_mode != MACHINE_MODE)) begin
      gen_delegation(hart);
    end
    // Setup trap vector register
    trap_vector_init(hart);
    // Setup PMP CSRs
    setup_pmp(hart);
    // Generate PMPADDR write test sequence
    gen_pmp_csr_write(hart);
    // Initialize PTE (link page table based on their real physical address)
    if(cfg.virtual_addr_translation_on) begin
      page_table_list.process_page_table(instr);
      gen_section(get_label("process_pt", hart), instr);
    end
    // Setup mepc register, jump to init entry
    setup_epc(hart);
    // Initialization of any implementation-specific custom CSRs
    setup_custom_csrs(hart);
    // Setup initial privilege mode
    gen_privileged_mode_switch_routine(hart);
  endfunction

  virtual function void gen_privileged_mode_switch_routine(int hart);
    privil_seq = riscv_privileged_common_seq::type_id::create("privil_seq");
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      string instr[$];
      string csr_handshake[$];
      string ret_instr;
      if(riscv_instr_pkg::supported_privileged_mode[i] != cfg.init_privileged_mode) continue;
      `uvm_info(`gfn, $sformatf("Generating privileged mode routing for %0s",
                      riscv_instr_pkg::supported_privileged_mode[i].name()), UVM_LOW)
      // Enter privileged mode
      privil_seq.cfg = cfg;
      privil_seq.hart = hart;
      `DV_CHECK_RANDOMIZE_FATAL(privil_seq)
      privil_seq.enter_privileged_mode(riscv_instr_pkg::supported_privileged_mode[i], instr);
      if (cfg.require_signature_addr) begin
        ret_instr = instr.pop_back();
        // Want to write the main system CSRs to the testbench before indicating that initialization
        // is complete, for any initial state analysis
        case(riscv_instr_pkg::supported_privileged_mode[i])
          SUPERVISOR_MODE: begin
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR),
                                    .csr(SSTATUS));
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR),
                                    .csr(SIE));
          end
          USER_MODE: begin
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR),
                                    .csr(USTATUS));
            gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(UIE));
          end
          default: `uvm_info(`gfn, $sformatf("Unsupported privileged_mode %0s",
                                   riscv_instr_pkg::supported_privileged_mode[i]), UVM_LOW)
        endcase
        // Write M-mode CSRs to testbench by default, as these should be implemented
        gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(MSTATUS));
        gen_signature_handshake(.instr(csr_handshake), .signature_type(WRITE_CSR), .csr(MIE));
        format_section(csr_handshake);
        instr = {instr, csr_handshake, ret_instr};
      end
      instr_stream = {instr_stream, instr};
    end
  endfunction

  // Setup EPC before entering target privileged mode
  virtual function void setup_epc(int hart);
    string instr[$];
    string mode_name;
    instr = {$sformatf("la x%0d, %0sinit", cfg.gpr[0], hart_prefix(hart))};
    if(cfg.virtual_addr_translation_on) begin
      // For supervisor and user mode, use virtual address instead of physical address.
      // Virtual address starts from address 0x0, here only the lower 12 bits are kept
      // as virtual address offset.
      instr = {instr,
               $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 12),
               $sformatf("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 12)};
    end
    mode_name = cfg.init_privileged_mode.name();
    instr.push_back($sformatf("csrw 0x%0x, x%0d", MEPC, cfg.gpr[0]));
    gen_section(get_label("mepc_setup", hart), instr);
  endfunction

  // Setup PMP CSR configuration
  virtual function void setup_pmp(int hart);
    string instr[$];
    if (riscv_instr_pkg::support_pmp) begin
      cfg.pmp_cfg.setup_pmp();
      cfg.pmp_cfg.gen_pmp_instr('{cfg.scratch_reg, cfg.gpr[0]}, instr);
      gen_section(get_label("pmp_setup", hart), instr);
    end
  endfunction

  // Generates a directed stream of instructions to write random values to all supported
  // pmpaddr CSRs to test write accessibility.
  // The original CSR values are restored afterwards.
  virtual function void gen_pmp_csr_write(int hart);
    string instr[$];
    if (riscv_instr_pkg::support_pmp && cfg.pmp_cfg.enable_write_pmp_csr) begin
      cfg.pmp_cfg.gen_pmp_write_test({cfg.scratch_reg, cfg.pmp_reg}, instr);
      gen_section(get_label("pmp_csr_write_test", hart), instr);
    end
  endfunction

  // Handles creation of a subroutine to initialize any custom CSRs
  virtual function void setup_custom_csrs(int hart);
    string instr[$];
    init_custom_csr(instr);
    gen_section(get_label("custom_csr_setup", hart), instr);
  endfunction

  // This function should be overridden in the riscv_asm_program_gen extended class
  // corresponding to the RTL implementation if it has any custom CSRs defined.
  //
  // All that needs to be done in the overridden function is to manually create
  // the instruction strings to set up any custom CSRs and then to push those strings
  // into the instr queue.
  virtual function void init_custom_csr(ref string instr[$]);
    instr.push_back("nop");
  endfunction

  //---------------------------------------------------------------------------------------
  // Privileged CSR setup for interrupt and exception handling and delegation
  //---------------------------------------------------------------------------------------

  // Interrupt and exception delegation setting.
  // The lower level exception and interrupt can be delegated to higher level handler.
  virtual function void gen_delegation(int hart);
    gen_delegation_instr(hart, MEDELEG, MIDELEG,
                         cfg.m_mode_exception_delegation,
                         cfg.m_mode_interrupt_delegation);
    if(riscv_instr_pkg::support_umode_trap) begin
      gen_delegation_instr(hart, SEDELEG, SIDELEG,
                           cfg.s_mode_exception_delegation,
                           cfg.s_mode_interrupt_delegation);
    end
  endfunction

  virtual function void gen_delegation_instr(int hart,
                                             privileged_reg_t edeleg,
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
    instr = {$sformatf("li x%0d, 0x%0x", cfg.gpr[0], deleg_val),
             $sformatf("csrw 0x%0x, x%0d # %0s", edeleg, cfg.gpr[0], edeleg.name())};
    // Interrupt delegation setup
    deleg_val = '0;
    foreach(ideleg_enable[cause]) begin
      if(ideleg_enable[cause]) begin
        deleg_val = deleg_val | (1 << int'(cause));
      end
    end
    instr = {instr,
             $sformatf("li x%0d, 0x%0x", cfg.gpr[0], deleg_val),
             $sformatf("csrw 0x%0x, x%0d # %0s", ideleg, cfg.gpr[0], ideleg.name())};
    section_name = edeleg.name();
    section_name = section_name.tolower();
    gen_section(get_label($sformatf("%0s_setup", section_name), hart), instr);
  endfunction

  // Setup trap vector - MTVEC, STVEC, UTVEC
  virtual function void trap_vector_init(int hart);
    string instr[];
    privileged_reg_t trap_vec_reg;
    string tvec_name;
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      case(riscv_instr_pkg::supported_privileged_mode[i])
        MACHINE_MODE:    trap_vec_reg = MTVEC;
        SUPERVISOR_MODE: trap_vec_reg = STVEC;
        USER_MODE:       trap_vec_reg = UTVEC;
        default: `uvm_info(`gfn, $sformatf("Unsupported privileged_mode %0s",
                           riscv_instr_pkg::supported_privileged_mode[i]), UVM_LOW)
      endcase
      // Skip utvec init if trap delegation to u_mode is not supported
      if ((riscv_instr_pkg::supported_privileged_mode[i] == USER_MODE) &&
          !riscv_instr_pkg::support_umode_trap) continue;
      if (riscv_instr_pkg::supported_privileged_mode[i] < cfg.init_privileged_mode) continue;
      tvec_name = trap_vec_reg.name();
      instr = {instr, $sformatf("la x%0d, %0s%0s_handler",
                                cfg.gpr[0], hart_prefix(hart), tvec_name.tolower())};
      if (SATP_MODE != BARE && riscv_instr_pkg::supported_privileged_mode[i] != MACHINE_MODE) begin
        // For supervisor and user mode, use virtual address instead of physical address.
        // Virtual address starts from address 0x0, here only the lower 20 bits are kept
        // as virtual address offset.
        instr = {instr,
                 $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 20),
                 $sformatf("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN - 20)};
      end
      instr = {instr, $sformatf("ori x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], cfg.mtvec_mode)};
      instr = {instr, $sformatf("csrw 0x%0x, x%0d # %0s",
                                 trap_vec_reg, cfg.gpr[0], trap_vec_reg.name())};
    end
    gen_section(get_label("trap_vec_init", hart), instr);
  endfunction

  //---------------------------------------------------------------------------------------
  // Exception handling routine
  //---------------------------------------------------------------------------------------

  // Trap handling routine
  virtual function void gen_all_trap_handler(int hart);
    string instr[$];
    // If PMP isn't supported, generate the relevant trap handler sections as per usual
    if (!riscv_instr_pkg::support_pmp) begin
      gen_trap_handlers(hart);
      // Ecall handler
      gen_ecall_handler(hart);
      // Instruction fault handler
      gen_instr_fault_handler(hart);
      // Load fault handler
      gen_load_fault_handler(hart);
      // Store fault handler
      gen_store_fault_handler(hart);
    end
    // Ebreak handler
    gen_ebreak_handler(hart);
    // Illegal instruction handler
    gen_illegal_instr_handler(hart);
    // Generate page table fault handling routine
    // Page table fault is always handled in machine mode, as virtual address translation may be
    // broken when page fault happens.
    gen_signature_handshake(instr, CORE_STATUS, HANDLING_EXCEPTION);
    if(page_table_list != null) begin
      page_table_list.gen_page_fault_handling_routine(instr);
    end else begin
      instr.push_back("nop");
    end
    gen_section(get_label("pt_fault_handler", hart), instr);
  endfunction

  virtual function void gen_trap_handlers(int hart);
    foreach(riscv_instr_pkg::supported_privileged_mode[i]) begin
      if(riscv_instr_pkg::supported_privileged_mode[i] < cfg.init_privileged_mode) continue;
      case(riscv_instr_pkg::supported_privileged_mode[i])
        MACHINE_MODE:
          gen_trap_handler_section(hart, "m", MCAUSE, MTVEC, MTVAL,
                                   MEPC, MSCRATCH, MSTATUS, MIE, MIP);
        SUPERVISOR_MODE:
          gen_trap_handler_section(hart, "s", SCAUSE, STVEC, STVAL,
                                   SEPC, SSCRATCH, SSTATUS, SIE, SIP);
        USER_MODE:
          if(riscv_instr_pkg::support_umode_trap) begin
            gen_trap_handler_section(hart, "u", UCAUSE, UTVEC, UTVAL,
                                     UEPC, USCRATCH, USTATUS, UIE, UIP);
          end
        default: `uvm_fatal(`gfn, $sformatf("Unsupported privileged_mode %0s",
                            riscv_instr_pkg::supported_privileged_mode[i]))
      endcase
    end
  endfunction

  // Generate the interrupt and trap handler for different privileged mode.
  // The trap handler checks the xCAUSE to determine the type of the exception and jumps to
  // corresponding exeception handling routine.
  virtual function void gen_trap_handler_section(int hart,
                                                 string mode,
                                                 privileged_reg_t cause, privileged_reg_t tvec,
                                                 privileged_reg_t tval, privileged_reg_t epc,
                                                 privileged_reg_t scratch, privileged_reg_t status,
                                                 privileged_reg_t ie, privileged_reg_t ip);
    bit is_interrupt = 'b1;
    string tvec_name;
    string instr[$];
    if (cfg.mtvec_mode == VECTORED) begin
      gen_interrupt_vector_table(hart, mode, status, cause, ie, ip, scratch, instr);
    end else begin
      // Push user mode GPR to kernel stack before executing exception handling, this is to avoid
      // exception handling routine modify user program state unexpectedly
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
      // Checking xStatus can be optional if ISS (like spike) has different implementation of
      // certain fields compared with the RTL processor.
      if (cfg.check_xstatus) begin
        instr = {instr, $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], status, status.name())};
      end
      instr = {instr,
               // Use scratch CSR to save a GPR value
               // Check if the exception is caused by an interrupt, if yes, jump to interrupt
               // handler Interrupt is indicated by xCause[XLEN-1]
               $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause.name()),
               $sformatf("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN-1),
               $sformatf("bne x%0d, x0, %0s%0smode_intr_handler",
                         cfg.gpr[0], hart_prefix(hart), mode)};
    end
    // The trap handler will occupy one 4KB page, it will be allocated one entry in the page table
    // with a specific privileged mode.
    if (SATP_MODE != BARE) begin
      instr_stream.push_back(".align 12");
    end else begin
      instr_stream.push_back($sformatf(".align %d", cfg.tvec_alignment));
    end
    tvec_name = tvec.name();
    gen_section(get_label($sformatf("%0s_handler", tvec_name.tolower()), hart), instr);
    // Exception handler
    instr = {};
    if (cfg.mtvec_mode == VECTORED) begin
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    end
    gen_signature_handshake(instr, CORE_STATUS, HANDLING_EXCEPTION);
    instr = {instr,
             // The trap is caused by an exception, read back xCAUSE, xEPC to see if these
             // CSR values are set properly. The checking is done by comparing against the log
             // generated by ISA simulator (spike).
             $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], epc, epc.name()),
             $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause.name()),
             // Breakpoint
             $sformatf("li x%0d, 0x%0x # BREAKPOINT", cfg.gpr[1], BREAKPOINT),
             $sformatf("beq x%0d, x%0d, %0sebreak_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             // Check if it's an ECALL exception. Jump to ECALL exception handler
             $sformatf("li x%0d, 0x%0x # ECALL_UMODE", cfg.gpr[1], ECALL_UMODE),
             $sformatf("beq x%0d, x%0d, %0secall_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             $sformatf("li x%0d, 0x%0x # ECALL_SMODE", cfg.gpr[1], ECALL_SMODE),
             $sformatf("beq x%0d, x%0d, %0secall_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             $sformatf("li x%0d, 0x%0x # ECALL_MMODE", cfg.gpr[1], ECALL_MMODE),
             $sformatf("beq x%0d, x%0d, %0secall_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             // Page table fault or access fault conditions
             $sformatf("li x%0d, 0x%0x", cfg.gpr[1], INSTRUCTION_ACCESS_FAULT),
             $sformatf("beq x%0d, x%0d, %0sinstr_fault_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             $sformatf("li x%0d, 0x%0x", cfg.gpr[1], LOAD_ACCESS_FAULT),
             $sformatf("beq x%0d, x%0d, %0sload_fault_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             $sformatf("li x%0d, 0x%0x", cfg.gpr[1], STORE_AMO_ACCESS_FAULT),
             $sformatf("beq x%0d, x%0d, %0sstore_fault_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             $sformatf("li x%0d, 0x%0x", cfg.gpr[1], INSTRUCTION_PAGE_FAULT),
             $sformatf("beq x%0d, x%0d, %0spt_fault_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             $sformatf("li x%0d, 0x%0x", cfg.gpr[1], LOAD_PAGE_FAULT),
             $sformatf("beq x%0d, x%0d, %0spt_fault_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             $sformatf("li x%0d, 0x%0x", cfg.gpr[1], STORE_AMO_PAGE_FAULT),
             $sformatf("beq x%0d, x%0d, %0spt_fault_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             // Illegal instruction exception
             $sformatf("li x%0d, 0x%0x # ILLEGAL_INSTRUCTION", cfg.gpr[1], ILLEGAL_INSTRUCTION),
             $sformatf("beq x%0d, x%0d, %0sillegal_instr_handler",
                       cfg.gpr[0], cfg.gpr[1], hart_prefix(hart)),
             // Skip checking tval for illegal instruction as it's implementation specific
             $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[1], tval, tval.name()),
             // use JALR to jump to test_done.
             $sformatf("1: la x%0d, test_done", cfg.scratch_reg),
             $sformatf("jalr x1, x%0d, 0", cfg.scratch_reg)
           };
    gen_section(get_label($sformatf("%0smode_exception_handler", mode), hart), instr);
  endfunction

  // Generate for interrupt vector table
  virtual function void gen_interrupt_vector_table(int              hart,
                                                   string           mode,
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
                    $sformatf("j %0s%0smode_exception_handler", hart_prefix(hart), mode)};
    // Redirect the interrupt to the corresponding interrupt handler
    for (int i = 1; i < max_interrupt_vector_num; i++) begin
      instr.push_back($sformatf("j %0s%0smode_intr_vector_%0d", hart_prefix(hart), mode, i));
    end
    if (!cfg.disable_compressed_instr) begin
      instr = {instr, ".option rvc;"};
    end
    for (int i = 1; i < max_interrupt_vector_num; i++) begin
      string intr_handler[$];
      push_gpr_to_kernel_stack(status, scratch, cfg.mstatus_mprv, cfg.sp, cfg.tp, intr_handler);
      gen_signature_handshake(.instr(intr_handler), .signature_type(CORE_STATUS),
                              .core_status(HANDLING_IRQ));
      intr_handler = {intr_handler,
                      $sformatf("csrr x%0d, 0x%0x # %0s", cfg.gpr[0], cause, cause.name()),
                      // Terminate the test if xCause[31] != 0 (indicating exception)
                      $sformatf("srli x%0d, x%0d, 0x%0x", cfg.gpr[0], cfg.gpr[0], XLEN-1),
                      $sformatf("beqz x%0d, 1f", cfg.gpr[0])};
      gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(status));
      gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(cause));
      gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(ie));
      gen_signature_handshake(.instr(intr_handler), .signature_type(WRITE_CSR), .csr(ip));
      // Jump to commmon interrupt handling routine
      intr_handler = {intr_handler,
                      $sformatf("j %0s%0smode_intr_handler", hart_prefix(hart), mode),
                      $sformatf("1: la x%0d, test_done", cfg.scratch_reg),
                      $sformatf("jalr x0, x%0d, 0", cfg.scratch_reg)};
      gen_section(get_label($sformatf("%0smode_intr_vector_%0d", mode, i), hart), intr_handler);
    end
  endfunction

  // ECALL trap handler
  // It does some clean up like dump GPRs before communicating with host to terminate the test.
  // User can extend this function if some custom clean up routine is needed.
  virtual function void gen_ecall_handler(int hart);
    string instr[$];
    dump_perf_stats(instr);
    gen_register_dump(instr);
    instr.push_back($sformatf("la x%0d, write_tohost", cfg.scratch_reg));
    instr.push_back($sformatf("jalr x0, x%0d, 0", cfg.scratch_reg));
    gen_section(get_label("ecall_handler", hart), instr);
  endfunction

  // Ebreak trap handler
  // When breakpoint exception happens, epc will be written with ebreak instruction
  // itself. Add epc by 4 and resume execution.
  // Note the breakpoint could be triggered by a C.EBREAK instruction, the generated program
  // guarantees that epc + 4 is a valid instruction boundary
  // TODO: Support random operations in debug mode
  // TODO: Support ebreak exception delegation
  // TODO: handshake the correct Xcause CSR based on delegation privil. mode
  virtual function void gen_ebreak_handler(int hart);
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, EBREAK_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    instr = {instr,
            $sformatf("csrr  x%0d, 0x%0x", cfg.gpr[0], MEPC),
            $sformatf("addi  x%0d, x%0d, 4", cfg.gpr[0], cfg.gpr[0]),
            $sformatf("csrw  0x%0x, x%0d", MEPC, cfg.gpr[0])
    };
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("ebreak_handler", hart), instr);
  endfunction

  // Illegal instruction handler
  // Note: Save the illegal instruction to MTVAL is optional in the spec, and mepc could be
  // a virtual address that cannot be used in machine mode handler. As a result, there's no way to
  // know the illegal instruction is compressed or not. This hanlder just simply adds the PC by
  // 4 and resumes execution. The way that the illegal instruction is injected guarantees that
  // PC + 4 is a valid instruction boundary.
  // TODO: handshake the corret Xcause CSR based on delegation setup
  virtual function void gen_illegal_instr_handler(int hart);
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, ILLEGAL_INSTR_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    instr = {instr,
            $sformatf("csrr  x%0d, 0x%0x", cfg.gpr[0], MEPC),
            $sformatf("addi  x%0d, x%0d, 4", cfg.gpr[0], cfg.gpr[0]),
            $sformatf("csrw  0x%0x, x%0d", MEPC, cfg.gpr[0])
    };
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("illegal_instr_handler", hart), instr);
  endfunction

  // TODO: handshake correct csr based on delegation
  virtual function void gen_instr_fault_handler(int hart);
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, INSTR_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    if (cfg.pmp_cfg.enable_pmp_exception_handler) begin
      cfg.pmp_cfg.gen_pmp_exception_routine({cfg.gpr, cfg.scratch_reg, cfg.pmp_reg},
                                            INSTRUCTION_ACCESS_FAULT,
                                            instr);
    end
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("instr_fault_handler", hart), instr);
  endfunction

  // TODO: handshake correct csr based on delegation
  virtual function void gen_load_fault_handler(int hart);
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, LOAD_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    if (cfg.pmp_cfg.enable_pmp_exception_handler) begin
      cfg.pmp_cfg.gen_pmp_exception_routine({cfg.gpr, cfg.scratch_reg, cfg.pmp_reg},
                                            LOAD_ACCESS_FAULT,
                                            instr);
    end
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("load_fault_handler", hart), instr);
  endfunction

  // TODO: handshake correct csr based on delegation
  virtual function void gen_store_fault_handler(int hart);
    string instr[$];
    gen_signature_handshake(instr, CORE_STATUS, STORE_FAULT_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));
    if (cfg.pmp_cfg.enable_pmp_exception_handler) begin
      cfg.pmp_cfg.gen_pmp_exception_routine({cfg.gpr, cfg.scratch_reg, cfg.pmp_reg},
                                            STORE_AMO_ACCESS_FAULT,
                                            instr);
    end
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("store_fault_handler", hart), instr);
  endfunction

  //---------------------------------------------------------------------------------------
  // Page table setup
  //---------------------------------------------------------------------------------------

  // Create page table if virtual address translation is supported.
  // The page is created based on the address translation mode - SV32, SV39, SV48
  // Right now only the lowest level 4KB page table is configured as leaf page table entry (PTE),
  // all the other super pages are link PTE.
  virtual function void create_page_table(int hart);
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
  virtual function void gen_page_table_section(int hart);
    string page_table_section[$];
    if(page_table_list != null) begin
      if (cfg.use_push_data_section) begin
        instr_stream.push_back($sformatf(".pushsection .%0spage_table,\"aw\",@progbits;",
                                         hart_prefix(hart)));
      end else begin
        instr_stream.push_back($sformatf(".section .%0spage_table,\"aw\",@progbits;",
                                         hart_prefix(hart)));
      end
      foreach(page_table_list.page_table[i]) begin
        page_table_list.page_table[i].gen_page_table_section(page_table_section);
        instr_stream = {instr_stream, page_table_section};
      end
      if (cfg.use_push_data_section) begin
        instr_stream.push_back(".popsection;");
      end
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
  virtual function void gen_interrupt_handler_section(privileged_mode_t mode, int hart);
    string mode_prefix;
    string ls_unit;
    privileged_reg_t status, ip, ie, scratch;
    string interrupt_handler_instr[$];
    ls_unit = (XLEN == 32) ? "w" : "d";
    if (mode < cfg.init_privileged_mode) return;
    if (mode == USER_MODE && !riscv_instr_pkg::support_umode_trap) return;
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
      // If nested interrupts are enabled, set xSTATUS.xIE in the interrupt handler
      // to re-enable interrupt handling capabilities
      if (cfg.enable_nested_interrupt) begin
        interrupt_handler_instr.push_back($sformatf("csrr x%0d, 0x%0x", cfg.gpr[0], scratch));
        interrupt_handler_instr.push_back($sformatf("bgtz x%0d, 1f", cfg.gpr[0]));
        interrupt_handler_instr.push_back($sformatf("csrwi 0x%0x, 0x1", scratch));
        case (status)
          MSTATUS: begin
            interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 8));
          end
          SSTATUS: begin
            interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 2));
          end
          USTATUS: begin
            interrupt_handler_instr.push_back($sformatf("csrsi 0x%0x, 0x%0x", status, 1));
          end
          default: `uvm_fatal(`gfn, $sformatf("Unsupported status %0s", status))
        endcase
        interrupt_handler_instr.push_back($sformatf("1: csrwi 0x%0x,0", scratch));
      end
    // Read back interrupt related privileged CSR
    // The value of these CSR are checked by comparing with spike simulation result.
    interrupt_handler_instr = {
           interrupt_handler_instr,
           $sformatf("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], status, status.name()),
           $sformatf("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], ie, ie.name()),
           $sformatf("csrr  x%0d, 0x%0x # %0s;", cfg.gpr[0], ip, ip.name()),
           // Clean all the pending interrupt
           $sformatf("csrrc x%0d, 0x%0x, x%0d # %0s;",
                     cfg.gpr[0], ip, cfg.gpr[0], ip.name())
    };
    gen_plic_section(interrupt_handler_instr);
    // Restore user mode GPR value from kernel stack before return
    pop_gpr_from_kernel_stack(status, scratch, cfg.mstatus_mprv,
                              cfg.sp, cfg.tp, interrupt_handler_instr);
    interrupt_handler_instr = {interrupt_handler_instr,
                               $sformatf("%0sret;", mode_prefix)
    };
    if (SATP_MODE != BARE) begin
      // The interrupt handler will use one 4KB page
      instr_stream.push_back(".align 12");
    end else begin
      instr_stream.push_back(".align 2");
    end
    gen_section(get_label($sformatf("%0smode_intr_handler", mode_prefix), hart),
                interrupt_handler_instr);
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
  virtual function void dump_perf_stats(ref string instr[$]);
    foreach(implemented_csr[i]) begin
      if (implemented_csr[i] inside {[MCYCLE:MHPMCOUNTER31H]}) begin
        gen_signature_handshake(.instr(instr),
                                .signature_type(WRITE_CSR),
                                .csr(implemented_csr[i]));
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
      str = {$sformatf("li x%0d, 0x%0h", cfg.gpr[1], cfg.signature_addr)};
      instr = {instr, str};
      case (signature_type)
        // A single data word is written to the signature address.
        // Bits [7:0] contain the signature_type of CORE_STATUS, and the upper
        // XLEN-8 bits contain the core_status_t data.
        CORE_STATUS: begin
          str = {$sformatf("li x%0d, 0x%0h", cfg.gpr[0], core_status),
                 $sformatf("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
                 $sformatf("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
                           cfg.gpr[0], signature_type),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])};
          instr = {instr, str};
        end
        // A single data word is written to the signature address.
        // Bits [7:0] contain the signature_type of TEST_RESULT, and the upper
        // XLEN-8 bits contain the test_result_t data.
        TEST_RESULT: begin
          str = {$sformatf("li x%0d, 0x%0h", cfg.gpr[0], test_result),
                 $sformatf("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
                 $sformatf("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
                           cfg.gpr[0], signature_type),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])};
          instr = {instr, str};
        end
        // The first write to the signature address contains just the
        // signature_type of WRITE_GPR.
        // It is followed by 32 consecutive writes to the signature address,
        // each writing the data contained in one GPR, starting from x0 as the
        // first write, and ending with x31 as the 32nd write.
        WRITE_GPR: begin
          str = {$sformatf("li x%0d, 0x%0h", cfg.gpr[0], signature_type),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])};
          instr = {instr, str};
          for(int i = 0; i < 32; i++) begin
            str = {$sformatf("sw x%0x, 0(x%0d)", i, cfg.gpr[1])};
            instr = {instr, str};
          end
        end
        // The first write to the signature address contains the
        // signature_type of WRITE_CSR in bits [7:0], and the CSR address in
        // the upper XLEN-8 bits.
        // It is followed by a second write to the signature address,
        // containing the data stored in the specified CSR.
        WRITE_CSR: begin
          if (!(csr inside {implemented_csr})) begin
            return;
          end
          str = {$sformatf("li x%0d, 0x%0h", cfg.gpr[0], csr),
                 $sformatf("slli x%0d, x%0d, 8", cfg.gpr[0], cfg.gpr[0]),
                 $sformatf("addi x%0d, x%0d, 0x%0h", cfg.gpr[0],
                           cfg.gpr[0], signature_type),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1]),
                 $sformatf("csrr x%0d, 0x%0h", cfg.gpr[0], csr),
                 $sformatf("sw x%0d, 0(x%0d)", cfg.gpr[0], cfg.gpr[1])};
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
    `uvm_info(`gfn, $sformatf("Adding directed instruction stream:%0s ratio:%0d/1000", name, ratio),
              UVM_LOW)
  endfunction

  virtual function void get_directed_instr_stream();
    string args, val;
    string stream_name_opts, stream_freq_opts;
    string stream_name;
    int stream_freq;
    string opts[$];
    for (int i=0; i<cfg.max_directed_instr_stream_seq; i++) begin
      args = $sformatf("directed_instr_%0d=", i);
      stream_name_opts = $sformatf("stream_name_%0d=", i);
      stream_freq_opts = $sformatf("stream_freq_%0d=", i);
      if ($value$plusargs({args,"%0s"}, val)) begin
        uvm_split_string(val, ",", opts);
        if (opts.size() != 2) begin
          `uvm_fatal(`gfn, $sformatf(
            "Incorrect directed instruction format : %0s, expect: name,ratio", val))
        end else begin
          add_directed_instr_stream(opts[0], opts[1].atoi());
        end
      end else if ($value$plusargs({stream_name_opts,"%0s"}, stream_name) &&
                   $value$plusargs({stream_freq_opts,"%0d"}, stream_freq)) begin
        add_directed_instr_stream(stream_name, stream_freq);
      end
    end
  endfunction

  // Generate directed instruction stream based on the ratio setting
  virtual function void generate_directed_instr_stream(input int hart,
                                                       input string label,
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
          new_instr_stream.hart = hart;
          new_instr_stream.label = $sformatf("%0s_%0d", label, idx);
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
  // Generate the debug ROM, and any related programs
  //---------------------------------------------------------------------------------------

  virtual function void gen_debug_rom(int hart);
    `uvm_info(`gfn, "Creating debug ROM", UVM_LOW)
    debug_rom = riscv_asm_program_gen::type_id::create("debug_rom", , {"uvm_test_top", ".", `gfn});
    debug_rom.cfg = cfg;
    debug_rom.hart = hart;
    debug_rom.gen_program();
    instr_stream = {instr_stream, debug_rom.instr_stream};
  endfunction

  //---------------------------------------------------------------------------------------
  // Vector extension generation
  //---------------------------------------------------------------------------------------

  virtual function void randomize_vec_gpr_and_csr();
    string lmul;
    if (!(RVV inside {supported_isa})) return;
    instr_stream.push_back({indent, $sformatf("csrwi vxsat, %0d", cfg.vector_cfg.vxsat)});
    instr_stream.push_back({indent, $sformatf("csrwi vxrm, %0d", cfg.vector_cfg.vxrm)});
    init_vec_gpr(); // GPR init uses a temporary SEW/LMUL setting before the final value set below.
    instr_stream.push_back($sformatf("li x%0d, %0d", cfg.gpr[1], cfg.vector_cfg.vl));
    if ((cfg.vector_cfg.vtype.vlmul > 1) && (cfg.vector_cfg.vtype.fractional_lmul)) begin
      lmul = $sformatf("mf%0d", cfg.vector_cfg.vtype.vlmul);
    end else begin
      lmul = $sformatf("m%0d", cfg.vector_cfg.vtype.vlmul);
    end
    instr_stream.push_back($sformatf("%svsetvli x%0d, x%0d, e%0d, %0s, d%0d",
                                     indent,
                                     cfg.gpr[0],
                                     cfg.gpr[1],
                                     cfg.vector_cfg.vtype.vsew,
                                     lmul,
                                     cfg.vector_cfg.vtype.vediv));
  endfunction

endclass
