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
  mem_region_t    data_page[$];

  `uvm_object_utils(riscv_mem_access_stream)
  `uvm_object_new

  function void pre_randomize();
    if(kernel_mode) begin
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
    if(kernel_mode) begin
      la_instr.imm_str = $sformatf("%s+%0d", cfg.s_mem_region[id].name, base);
    end else begin
      la_instr.imm_str = $sformatf("%s+%0d", cfg.mem_region[id].name, base);
    end
    instr_list.push_front(la_instr);
  endfunction

  // Insert some other instructions to mix with mem_access instruction
  virtual function void add_mixed_instr(int instr_cnt);
    riscv_instr_base instr;
    setup_allowed_instr(1, 1);
    for(int i = 0; i < instr_cnt; i ++) begin
      instr = riscv_instr_base::type_id::create("instr");
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

  riscv_instr_base     jump;
  riscv_instr_base     addi;
  riscv_pseudo_instr   la;
  riscv_instr_base     branch;
  rand riscv_reg_t     gpr;
  rand int             imm;
  rand bit             enable_branch;
  rand int             mixed_instr_cnt;
  riscv_instr_base     stack_exit_instr[];
  string               target_program_label;
  int                  idx;
  bit                  use_jalr;

  constraint instr_c {
    !(gpr inside {cfg.reserved_regs, ZERO});
    imm inside {[-1023:1023]};
    mixed_instr_cnt inside {[5:10]};
  }

  `uvm_object_utils(riscv_jump_instr)

  function new(string name = "");
    super.new(name);
    jump = riscv_instr_base::type_id::create("jump");
    la = riscv_pseudo_instr::type_id::create("la");
    addi = riscv_instr_base::type_id::create("addi");
    branch = riscv_instr_base::type_id::create("branch");
  endfunction

  function void post_randomize();
    riscv_instr_base instr[];
    `DV_CHECK_RANDOMIZE_WITH_FATAL(jump,
      (use_jalr) -> (instr_name == JALR);
      instr_name dist {JAL := 2, JALR := 6, C_JALR := 2};
      if (cfg.disable_compressed_instr || (cfg.ra != RA)) {
        instr_name != C_JALR;
      }
      rd == cfg.ra;
      rs1 == gpr;
    )
    `DV_CHECK_RANDOMIZE_WITH_FATAL(addi,
      rs1 == gpr;
      instr_name == ADDI;
      rd  == gpr;
    )
    `DV_CHECK_RANDOMIZE_WITH_FATAL(branch,
      instr_name inside {BEQ, BNE, BLT, BGE, BLTU, BGEU};)
    la.pseudo_instr_name = LA;
    la.imm_str = target_program_label;
    la.rd = gpr;
    // Generate some random instructions to mix with jump instructions
    reserved_rd = {gpr};
    initialize_instr_list(mixed_instr_cnt);
    gen_instr(1'b1);
    addi.imm_str = $sformatf("%0d", imm);
    jump.imm_str = $sformatf("%0d", -imm);
    // The branch instruction is always inserted right before the jump instruction to avoid
    // skipping other required instructions like restore stack, load jump base etc.
    // The purse of adding the branch instruction here is to cover branch -> jump scenario.
    if(enable_branch) instr = {branch};
    // Restore stack before unconditional jump
    if(jump.rd == ZERO) begin
      instr= {stack_exit_instr, instr};
    end
    if(jump.instr_name == JAL) begin
      jump.imm_str = target_program_label;
    end else if (jump.instr_name == C_JALR) begin
      instr = {la, instr};
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
    jump.label = $sformatf("j_%0s_%0s_%0d", label, target_program_label, idx);
    branch.imm_str = jump.label;
    branch.comment = "branch to jump instr";
    branch.branch_assigned = 1'b1;
  endfunction
endclass

// Stress back to back jump instruction
class riscv_jal_instr extends riscv_rand_instr_stream;

  riscv_instr_base     jump[];
  riscv_instr_base     jump_start;
  riscv_instr_base     jump_end;
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
    jump_start = riscv_instr_base::type_id::create("jump_start");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(jump_start,
      instr_name == JAL;
      rd == cfg.ra;
    )
    jump_start.imm_str = $sformatf("%0df", order[0]);
    jump_start.label = label;
    // Last instruction
    jump_end = riscv_instr_base::type_id::create("jump_end");
    randomize_instr(jump_end);
    jump_end.label = $sformatf("%0d", num_of_jump_instr);
    foreach (jump[i]) begin
      jump[i] = riscv_instr_base::type_id::create($sformatf("jump_%0d", i));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(jump[i],
        instr_name inside {jal};
        rd dist {RA := 5, T1 := 2, [SP:T0] :/ 1, [T2:T6] :/ 2};
        !(rd inside {cfg.reserved_regs});
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
  riscv_instr_base         push_stack_instr[];
  riscv_reg_t              saved_regs[];
  rand riscv_rand_instr    branch_instr;
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
      push_stack_instr[i] = riscv_instr_base::type_id::
                             create($sformatf("push_stack_instr_%0d", i));
    end
    // addi sp,sp,-imm
    `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[0],
                                   instr_name == ADDI; rd == cfg.sp; rs1 == cfg.sp;
                                   imm == (~stack_len + 1);)
    push_stack_instr[0].imm_str = $sformatf("-%0d", stack_len);
    foreach(saved_regs[i]) begin
      if(XLEN == 32) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[i+1],
          instr_name == SW; rs2 == saved_regs[i]; rs1 == cfg.sp; imm == 4 * (i+1);)
      end else begin
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
      // Cover jal -> branch scenario, the branch is added before push stack operation
      branch_instr = riscv_rand_instr::type_id::create("branch_instr");
      branch_instr.cfg = cfg;
      `ifdef DSIM
        `DV_CHECK_RANDOMIZE_WITH_FATAL(branch_instr,
                                       instr_name inside {[BEQ:BGEU], C_BEQZ, C_BNEZ};)
      `else
        `DV_CHECK_RANDOMIZE_WITH_FATAL(branch_instr, category == BRANCH;)
      `endif
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

  int                      stack_len;
  int                      num_of_reg_to_save;
  int                      num_of_redudant_instr;
  riscv_instr_base         pop_stack_instr[];
  riscv_reg_t              saved_regs[];

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
      pop_stack_instr[i] = riscv_instr_base::type_id::
                             create($sformatf("pop_stack_instr_%0d", i));
    end
    foreach(saved_regs[i]) begin
      if(XLEN == 32) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[i],
          instr_name == LW; rd == saved_regs[i]; rs1 == cfg.sp; imm == 4 * (i+1);)
      end else begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[i],
          instr_name == LD; rd == saved_regs[i]; rs1 == cfg.sp; imm == 8 * (i+1);)
      end
      pop_stack_instr[i].process_load_store = 0;
    end
    // addi sp,sp,imm
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[num_of_reg_to_save],
      instr_name == ADDI; rd == cfg.sp; rs1 == cfg.sp; imm == stack_len;)
    pop_stack_instr[num_of_reg_to_save].imm_str = $sformatf("%0d", stack_len);
    mix_instr_stream(pop_stack_instr);
    foreach(instr_list[i]) begin
      instr_list[i].atomic = 1'b1;
      instr_list[i].has_label = 1'b0;
    end
  endfunction

endclass

// Cover the long fprward and backward jump
class riscv_long_branch_instr extends riscv_rand_instr_stream;

  int branch_instr_stream_len = 100;
  int branch_instr_offset = 999;
  riscv_rand_instr_stream forward_branch_instr_stream;
  riscv_rand_instr_stream backward_branch_instr_stream;
  riscv_instr_base        jump_instr;

  `uvm_object_utils(riscv_long_branch_instr)

  function new(string name = "");
    super.new(name);
    forward_branch_instr_stream = riscv_rand_instr_stream::type_id::
                                  create("forward_branch_instr_stream");
    backward_branch_instr_stream = riscv_rand_instr_stream::type_id::
                                  create("backward_branch_instr_stream");
    jump_instr = riscv_instr_base::type_id::create("jump_instr");
  endfunction

  function void init(int instr_len);
    branch_instr_stream_len = instr_len;
    initialize_instr_list(branch_instr_offset-branch_instr_stream_len);
    forward_branch_instr_stream.cfg = cfg;
    backward_branch_instr_stream.cfg = cfg;
    forward_branch_instr_stream.initialize_instr_list(branch_instr_stream_len);
    backward_branch_instr_stream.initialize_instr_list(branch_instr_stream_len);
  endfunction

  virtual function void gen_instr(bit no_branch = 1'b0, bit no_load_store = 1'b1,
                                  bit is_debug_program = 1'b0);
    int branch_offset;
    super.gen_instr(1'b1);
    forward_branch_instr_stream.gen_instr();
    backward_branch_instr_stream.gen_instr();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(jump_instr, instr_name == JAL;)
    jump_instr.imm_str = "test_done";
    instr_list = {forward_branch_instr_stream.instr_list, instr_list,
                  jump_instr, backward_branch_instr_stream.instr_list};
    foreach(instr_list[i]) begin
      instr_list[i].atomic = 1'b1;
      if(!instr_list[i].is_branch_target) begin
        instr_list[i].has_label = 1'b0;
      end
      if(instr_list[i].category == BRANCH) begin
        if(i < branch_instr_stream_len)
          branch_offset = branch_instr_offset;
        else
          branch_offset = -branch_instr_offset;
        instr_list[i].imm_str = $sformatf("target_%0d", i);
        instr_list[i].branch_assigned = 1'b1;
        // Avoid dead loop
        if(((instr_list[i+branch_offset].category == BRANCH) ||
             instr_list[i+branch_offset].is_branch_target) && (branch_offset < 0))
          branch_offset = branch_offset + 1;
        `uvm_info(get_full_name(), $sformatf("Branch [%0d] %0s -> [%0d] %0s", i,
                  instr_list[i].convert2asm(), i+branch_offset,
                  instr_list[i+branch_offset].convert2asm()), UVM_LOW)
        if(i < -branch_offset)
          `uvm_fatal(get_name(), $sformatf("Unexpected branch instr at %0d", i))
        instr_list[i+branch_offset].label = $sformatf("target_%0d", i);
        instr_list[i+branch_offset].has_label = 1'b1;
        instr_list[i+branch_offset].is_branch_target = 1;
      end
    end
  endfunction

endclass

class riscv_sw_interrupt_instr extends riscv_directed_instr_stream;

  rand bit usip;
  rand bit ssip;
  rand bit msip;
  rand privileged_reg_t ip_reg;
  rand riscv_pseudo_instr li_instr;
  rand riscv_instr_base csr_instr;
  riscv_privil_reg ip;
  rand riscv_reg_t rs1_reg;

  constraint ip_reg_c {
    if(cfg.init_privileged_mode == MACHINE_MODE) {
      ip_reg == MIP;
    } else {
      ip_reg == SIP;
    }
    (ip_reg == MIP) -> (usip || ssip || msip);
    (ip_reg == SIP) -> (usip || ssip);
  }

  constraint instr_c {
    !(rs1_reg inside {cfg.reserved_regs});
    rs1_reg != ZERO;
    li_instr.pseudo_instr_name == LI;
    li_instr.rd == rs1_reg;
    csr_instr.instr_name == CSRRW;
    csr_instr.rs1 == rs1_reg;
    // TODO: Support non-zero rd for SIP, MIP
    // csr_instr.rd inside {cfg.avail_regs};
    csr_instr.rd == ZERO;
    csr_instr.csr == ip_reg;
  }

  `uvm_object_utils(riscv_sw_interrupt_instr)

  function new(string name = "");
    super.new(name);
    li_instr = riscv_pseudo_instr::type_id::create("li_instr");
    csr_instr = riscv_instr_base::type_id::create("csr_instr");
    ip = riscv_privil_reg::type_id::create("ip");
  endfunction

  function void post_randomize();
    // TODO: Support UIP
    if(cfg.init_privileged_mode == USER_MODE) return;
    ip.init_reg(ip_reg);
    if(ip_reg == SIP) begin
      ip.set_field("USIP", usip);
      ip.set_field("SSIP", ssip);
    end else begin
      ip.set_field("USIP", usip);
      ip.set_field("SSIP", ssip);
      ip.set_field("MSIP", msip);
    end
    li_instr.imm_str = $sformatf("0x%0x", ip.get_val());
    csr_instr.comment = ip_reg.name();
    instr_list = {li_instr, csr_instr};
    super.post_randomize();
  endfunction

endclass

