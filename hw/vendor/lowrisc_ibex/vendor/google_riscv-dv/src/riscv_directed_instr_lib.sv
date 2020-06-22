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

// Base class for directed instruction stream
class riscv_directed_instr_stream extends riscv_rand_instr_stream;

  `uvm_object_utils(riscv_directed_instr_stream)

  string label;

  function new(string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    foreach(instr_list[i]) begin
      instr_list[i].has_label = 1'b0;
      instr_list[i].atomic = 1'b1;
    end
    instr_list[0].comment = $sformatf("Start %0s", get_name());
    instr_list[$].comment = $sformatf("End %0s", get_name());
    if(label!= "") begin
      instr_list[0].label = label;
      instr_list[0].has_label = 1'b1;
    end
  endfunction

endclass

// Base class for memory access stream
class riscv_mem_access_stream extends riscv_directed_instr_stream;

  int             max_data_page_id;
  bit             load_store_shared_memory;
  mem_region_t    data_page[$];

  `uvm_object_utils(riscv_mem_access_stream)
  `uvm_object_new

  function void pre_randomize();
    if (load_store_shared_memory) begin
      data_page = cfg.amo_region;
    end else if(kernel_mode) begin
      data_page = cfg.s_mem_region;
    end else begin
      data_page = cfg.mem_region;
    end
    max_data_page_id = data_page.size();
  endfunction

  // Use "la" instruction to initialize the base regiseter
  virtual function void add_rs1_init_la_instr(riscv_reg_t gpr, int id, int base = 0);
    riscv_pseudo_instr la_instr;
    la_instr = riscv_pseudo_instr::type_id::create("la_instr");
    la_instr.pseudo_instr_name = LA;
    la_instr.rd = gpr;
    if (load_store_shared_memory) begin
      la_instr.imm_str = $sformatf("%0s+%0d", cfg.amo_region[id].name, base);

    end else if(kernel_mode) begin
      la_instr.imm_str = $sformatf("%0s%0s+%0d",
                                   hart_prefix(hart), cfg.s_mem_region[id].name, base);
    end else begin
      la_instr.imm_str = $sformatf("%0s%0s+%0d",
                                   hart_prefix(hart), cfg.mem_region[id].name, base);
    end
    instr_list.push_front(la_instr);
  endfunction

  // Insert some other instructions to mix with mem_access instruction
  virtual function void add_mixed_instr(int instr_cnt);
    riscv_instr      instr;
    setup_allowed_instr(1, 1);
    for(int i = 0; i < instr_cnt; i ++) begin
      instr = riscv_instr::type_id::create("instr");
      randomize_instr(instr);
      insert_instr(instr);
    end
  endfunction

endclass

// Jump instruction (JAL, JALR)
// la rd0, jump_tagert_label
// addi rd1, offset, rd0
// jalr rd, offset, rd1
// For JAL, restore the stack before doing the jump
class riscv_jump_instr extends riscv_directed_instr_stream;

  riscv_instr          jump;
  riscv_instr          addi;
  riscv_pseudo_instr   la;
  riscv_instr          branch;
  rand riscv_reg_t     gpr;
  rand int             imm;
  rand bit             enable_branch;
  rand int             mixed_instr_cnt;
  riscv_instr          stack_exit_instr[];
  string               target_program_label;
  int                  idx;
  bit                  use_jalr;

  constraint instr_c {
    !(gpr inside {cfg.reserved_regs, ZERO});
    imm inside {[-1023:1023]};
    mixed_instr_cnt inside {[5:10]};
    if (jump.instr_name inside {C_JR, C_JALR}) {
      imm == 0;
    }
  }

  `uvm_object_utils(riscv_jump_instr)

  function new(string name = "");
    super.new(name);
    la = riscv_pseudo_instr::type_id::create("la");
  endfunction

  function void pre_randomize();
    if (use_jalr) begin
      jump = riscv_instr::get_instr(JALR);
    end else if (cfg.disable_compressed_instr || (cfg.ra != RA)) begin
      jump = riscv_instr::get_rand_instr(.include_instr({JAL, JALR}));
    end else begin
      jump = riscv_instr::get_rand_instr(.include_instr({JAL, JALR, C_JALR}));
    end
    addi = riscv_instr::get_instr(ADDI);
    branch = riscv_instr::get_rand_instr(.include_instr({BEQ, BNE, BLT, BGE, BLTU, BGEU}));
  endfunction

  function void post_randomize();
    riscv_instr instr[];
    `DV_CHECK_RANDOMIZE_WITH_FATAL(jump,
      if (has_rd) {
        rd == cfg.ra;
      }
      if (has_rs1) {
        rs1 == gpr;
      })
    `DV_CHECK_RANDOMIZE_WITH_FATAL(addi, rs1 == gpr; rd == gpr;)
    `DV_CHECK_RANDOMIZE_FATAL(branch)
    la.pseudo_instr_name = LA;
    la.imm_str = target_program_label;
    la.rd = gpr;
    // Generate some random instructions to mix with jump instructions
    reserved_rd = {gpr};
    initialize_instr_list(mixed_instr_cnt);
    gen_instr(1'b1);
    if (jump.instr_name inside {JALR, C_JALR}) begin
      // JALR is expected to set lsb to 0
      int offset = $urandom_range(0, 1);
      addi.imm_str = $sformatf("%0d", imm + offset);
    end else begin
      addi.imm_str = $sformatf("%0d", imm);
    end
    if (cfg.enable_misaligned_instr) begin
      // Jump to a misaligned address
      jump.imm_str = $sformatf("%0d", -imm + 2);
    end else begin
      jump.imm_str = $sformatf("%0d", -imm);
    end
    // The branch instruction is always inserted right before the jump instruction to avoid
    // skipping other required instructions like restore stack, load jump base etc.
    // The purse of adding the branch instruction here is to cover branch -> jump scenario.
    if(enable_branch) instr = {branch};
    // Restore stack before unconditional jump
    if((jump.rd == ZERO) || (jump.instr_name == C_JR)) begin
      instr= {stack_exit_instr, instr};
    end
    if(jump.instr_name == JAL) begin
      jump.imm_str = target_program_label;
    end else begin
      instr = {la, addi, instr};
    end
    mix_instr_stream(instr);
    instr_list = {instr_list, jump};
    foreach(instr_list[i]) begin
      instr_list[i].has_label = 1'b0;
      instr_list[i].atomic = 1'b1;
    end
    jump.has_label = 1'b1;
    jump.label = $sformatf("%0s_j%0d", label, idx);
    jump.comment = $sformatf("jump %0s -> %0s", label, target_program_label);
    branch.imm_str = jump.label;
    branch.comment = "branch to jump instr";
    branch.branch_assigned = 1'b1;
  endfunction
endclass

// Stress back to back jump instruction
class riscv_jal_instr extends riscv_rand_instr_stream;

  riscv_instr          jump[];
  riscv_instr          jump_start;
  riscv_instr          jump_end;
  rand int unsigned    num_of_jump_instr;
  riscv_instr_name_t   jal[$];

  constraint instr_c {
    num_of_jump_instr inside {[10:30]};
  }

  `uvm_object_utils(riscv_jal_instr)

  function new(string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    int order[];
    order = new[num_of_jump_instr];
    jump = new[num_of_jump_instr];
    foreach (order[i]) begin
      order[i] = i;
    end
    order.shuffle();
    setup_allowed_instr(1, 1);
    jal = {JAL};
    if (!cfg.disable_compressed_instr) begin
      jal.push_back(C_J);
      if (XLEN == 32) begin
        jal.push_back(C_JAL);
      end
    end
    // First instruction
    jump_start = riscv_instr::get_instr(JAL);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(jump_start, rd == cfg.ra;)
    jump_start.imm_str = $sformatf("%0df", order[0]);
    jump_start.label = label;
    // Last instruction
    randomize_instr(jump_end);
    jump_end.label = $sformatf("%0d", num_of_jump_instr);
    foreach (jump[i]) begin
      jump[i] = riscv_instr::get_rand_instr(.include_instr({jal}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(jump[i],
        if (has_rd) {
          rd dist {RA := 5, T1 := 2, [SP:T0] :/ 1, [T2:T6] :/ 2};
          !(rd inside {cfg.reserved_regs});
        }
      )
      jump[i].label = $sformatf("%0d", i);
    end
    foreach (order[i]) begin
      if (i == num_of_jump_instr - 1) begin
        jump[order[i]].imm_str = $sformatf("%0df", num_of_jump_instr);
      end else begin
        if (order[i+1] > order[i]) begin
          jump[order[i]].imm_str = $sformatf("%0df", order[i+1]);
        end else begin
          jump[order[i]].imm_str = $sformatf("%0db", order[i+1]);
        end
      end
    end
    instr_list = {jump_start, jump, jump_end};
    foreach (instr_list[i]) begin
      instr_list[i].has_label = 1'b1;
      instr_list[i].atomic = 1'b1;
    end
  endfunction
endclass

// Push stack instruction stream
class riscv_push_stack_instr extends riscv_rand_instr_stream;

  int                      stack_len;
  int                      num_of_reg_to_save;
  int                      num_of_redudant_instr;
  riscv_instr              push_stack_instr[];
  riscv_reg_t              saved_regs[];
  riscv_instr              branch_instr;
  rand bit                 enable_branch;
  string                   push_start_label;

  `uvm_object_utils(riscv_push_stack_instr)

  function new(string name = "");
    super.new(name);
  endfunction

  function void init();
    // Save RA, T0
    reserved_rd = {cfg.ra};
    saved_regs = {cfg.ra};
    num_of_reg_to_save = saved_regs.size();
    if(num_of_reg_to_save * (XLEN/8) > stack_len) begin
      `uvm_fatal(get_full_name(), $sformatf("stack len [%0d] is not enough to store %d regs",
                 stack_len, num_of_reg_to_save))
    end
    num_of_redudant_instr = $urandom_range(3,10);
    initialize_instr_list(num_of_redudant_instr);
  endfunction

  virtual function void gen_push_stack_instr(int stack_len, bit allow_branch = 1);
    this.stack_len = stack_len;
    init();
    gen_instr(1'b1);
    push_stack_instr = new[num_of_reg_to_save+1];
    foreach(push_stack_instr[i]) begin
      push_stack_instr[i] = riscv_instr::type_id::
                            create($sformatf("push_stack_instr_%0d", i));
    end
    // addi sp,sp,-imm
    push_stack_instr[0] = riscv_instr::get_instr(ADDI);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[0],
                                   rd == cfg.sp; rs1 == cfg.sp;
                                   imm == (~stack_len + 1);)
    push_stack_instr[0].imm_str = $sformatf("-%0d", stack_len);
    foreach(saved_regs[i]) begin
      if(XLEN == 32) begin
        push_stack_instr[i+1] = riscv_instr::get_instr(SW);
        `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[i+1],
          rs2 == saved_regs[i]; rs1 == cfg.sp; imm == 4 * (i+1);)
      end else begin
        push_stack_instr[i+1] = riscv_instr::get_instr(SD);
        `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[i+1],
          instr_name == SD; rs2 == saved_regs[i]; rs1 == cfg.sp; imm == 8 * (i+1);)
      end
      push_stack_instr[i+1].process_load_store = 0;
    end
    if (allow_branch) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(enable_branch)
    end else begin
      enable_branch = 0;
    end
    if(enable_branch) begin
      branch_instr = riscv_instr::get_rand_instr(.include_category({BRANCH}));
      `DV_CHECK_RANDOMIZE_FATAL(branch_instr)
      branch_instr.imm_str = push_start_label;
      branch_instr.branch_assigned = 1'b1;
      push_stack_instr[0].label = push_start_label;
      push_stack_instr[0].has_label = 1'b1;
      push_stack_instr = {branch_instr, push_stack_instr};
    end
    mix_instr_stream(push_stack_instr);
    foreach(instr_list[i]) begin
      instr_list[i].atomic = 1'b1;
      if(instr_list[i].label == "")
        instr_list[i].has_label = 1'b0;
    end
  endfunction

endclass

// Pop stack instruction stream
class riscv_pop_stack_instr extends riscv_rand_instr_stream;

  int          stack_len;
  int          num_of_reg_to_save;
  int          num_of_redudant_instr;
  riscv_instr  pop_stack_instr[];
  riscv_reg_t  saved_regs[];

  `uvm_object_utils(riscv_pop_stack_instr)

  function new(string name = "");
    super.new(name);
  endfunction

  function void init();
    reserved_rd = {cfg.ra};
    num_of_reg_to_save = saved_regs.size();
    if(num_of_reg_to_save * 4 > stack_len) begin
      `uvm_fatal(get_full_name(), $sformatf("stack len [%0d] is not enough to store %d regs",
                 stack_len, num_of_reg_to_save))
    end
    num_of_redudant_instr = $urandom_range(3,10);
    initialize_instr_list(num_of_redudant_instr);
  endfunction

  virtual function void gen_pop_stack_instr(int stack_len, riscv_reg_t saved_regs[]);
    this.stack_len = stack_len;
    this.saved_regs = saved_regs;
    init();
    gen_instr(1'b1);
    pop_stack_instr = new[num_of_reg_to_save+1];
    foreach(pop_stack_instr[i]) begin
      pop_stack_instr[i] = riscv_instr::type_id::
                           create($sformatf("pop_stack_instr_%0d", i));
    end
    foreach(saved_regs[i]) begin
      if(XLEN == 32) begin
        pop_stack_instr[i] = riscv_instr::get_instr(LW);
        `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[i],
          rd == saved_regs[i]; rs1 == cfg.sp; imm == 4 * (i+1);)
      end else begin
        pop_stack_instr[i] = riscv_instr::get_instr(LD);
        `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[i],
          rd == saved_regs[i]; rs1 == cfg.sp; imm == 8 * (i+1);)
      end
      pop_stack_instr[i].process_load_store = 0;
    end
    // addi sp,sp,imm
    pop_stack_instr[num_of_reg_to_save] = riscv_instr::get_instr(ADDI);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[num_of_reg_to_save],
                                   rd == cfg.sp; rs1 == cfg.sp; imm == stack_len;)
    pop_stack_instr[num_of_reg_to_save].imm_str = $sformatf("%0d", stack_len);
    mix_instr_stream(pop_stack_instr);
    foreach(instr_list[i]) begin
      instr_list[i].atomic = 1'b1;
      instr_list[i].has_label = 1'b0;
    end
  endfunction

endclass

// Strees the numeric corner cases of integer arithmetic operations
class riscv_int_numeric_corner_stream extends riscv_directed_instr_stream;

  typedef enum {
    NormalValue,
    Zero,
    AllOne,
    NegativeMax
  } int_numeric_e;

  int unsigned num_of_avail_regs = 10;
  rand int unsigned   num_of_instr;
  rand bit [XLEN-1:0] init_val[];
  rand int_numeric_e  init_val_type[];
  riscv_pseudo_instr  init_instr[];

  constraint init_val_c {
    solve init_val_type before init_val;
    init_val_type.size() == num_of_avail_regs;
    init_val.size() == num_of_avail_regs;
    num_of_instr inside {[15:30]};
  }

  constraint avail_regs_c {
    unique {avail_regs};
    foreach(avail_regs[i]) {
      !(avail_regs[i] inside {cfg.reserved_regs});
      avail_regs[i] != ZERO;
    }
  }

  `uvm_object_utils(riscv_int_numeric_corner_stream)
  `uvm_object_new

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    super.pre_randomize();
  endfunction : pre_randomize

  function void post_randomize();
    init_instr = new[num_of_avail_regs];
    foreach (init_val_type[i]) begin
      if (init_val_type[i] == Zero) begin
        init_val[i] = 0;
      end else if (init_val_type[i] == AllOne) begin
        init_val[i] = '1;
      end else if (init_val_type[i] == NegativeMax) begin
        init_val[i] = 1 << (XLEN-1);
      end
      init_instr[i] = new();
      init_instr[i].rd = avail_regs[i];
      init_instr[i].pseudo_instr_name = LI;
      init_instr[i].imm_str = $sformatf("0x%0x", init_val[i]);
      instr_list.push_back(init_instr[i]);
    end
    for (int i = 0; i < num_of_instr; i++) begin
      riscv_instr instr = riscv_instr::get_rand_instr(
        .include_category({ARITHMETIC}),
        .exclude_group({RV32C, RV64C, RV32F, RV64F, RV32D, RV64D}));
      randomize_gpr(instr);
      instr_list.push_back(instr);
    end
    super.post_randomize();
  endfunction

endclass : riscv_int_numeric_corner_stream
