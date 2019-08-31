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

// Create a infinte zero instruction loop, test if we can interrupt or
// enter debug mode while core is executing this loop
class riscv_infinte_loop_instr extends riscv_directed_instr_stream;

  string label_prefix = "";
  string label_name;

  `uvm_object_utils(riscv_infinte_loop_instr)

  constraint instr_c {
    foreach(instr_list[i]) {
      instr_list[i].imm == 0;
      instr_list[i].category inside {JUMP, BRANCH};
      instr_list[i].instr_name != JALR;
    }
  }

  function new(string name = "");
    super.new(name);
  endfunction

  function void pre_randomize();
    riscv_rand_instr instr;
    initialize_instr_list(5);
    foreach(instr_list[i]) begin
      $cast(instr, instr_list[i]);
      instr.constraint_cfg_knob_c.constraint_mode(0);
    end
  endfunction

  function void post_randomize();
    foreach(instr_list[i]) begin
      label_name = $sformatf("%0s_inf_loop_%0d", label_prefix, i);
      instr_list[i].atomic = 1'b1;
      instr_list[i].label = label_name;
      instr_list[i].imm_str = label_name;
      instr_list[i].has_label = 1'b1;
      instr_list[i].branch_assigned = 1'b1;
    end
  endfunction

endclass

// Jump instruction (JAL, JALR)
// la rd0, jump_tagert_label
// addi rd1, offset, rd0
// jalr rd, offset, rd1
// For JAL, restore the stack before doing the jump
class riscv_jump_instr extends riscv_rand_instr_stream;

  rand riscv_instr_base    jump;
  rand riscv_instr_base    addi;
  rand riscv_pseudo_instr  la;
  rand riscv_instr_base    branch;
  rand bit                 enable_branch;
  rand int                 mixed_instr_cnt;
  riscv_instr_base         stack_exit_instr[];
  string                   target_program_label;
  int                      idx;

  constraint instr_c {
    solve jump.instr_name before addi.imm;
    solve jump.instr_name before addi.rs1;
    jump.instr_name dist {JAL := 1, JALR := 1};
    jump.rd == RA;
    !(addi.rs1 inside {cfg.reserved_regs, ZERO});
    addi.rs1 == la.rd;
    addi.rd  == la.rd;
    // Avoid using negative offset -1024
    addi.imm != 'hFFFF_FC00;
    jump.imm == ~addi.imm + 1;
    jump.rs1 == addi.rd;
    addi.instr_name == ADDI;
    branch.category == BRANCH;
    la.pseudo_instr_name == LA;
    soft mixed_instr_cnt inside {[5:10]};
  }

  `uvm_object_utils(riscv_jump_instr)

  function new(string name = "");
    super.new(name);
    jump = riscv_instr_base::type_id::create("jump");
    la = riscv_pseudo_instr::type_id::create("la");
    addi = riscv_instr_base::type_id::create("addi");
    branch = riscv_instr_base::type_id::create("branch");
    instr_list.rand_mode(0);
  endfunction

  function void post_randomize();
    riscv_instr_base instr[];
    // Generate some random instructions to mix with jump instructions
    reserved_rd = {addi.rs1};
    initialize_instr_list(mixed_instr_cnt);
    gen_instr(1'b1);
    la.imm_str = target_program_label;
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

// Push stack instruction stream
class riscv_push_stack_instr extends riscv_rand_instr_stream;

  int                      stack_len;
  int                      num_of_reg_to_save;
  int                      num_of_redudant_instr;
  riscv_instr_base         push_stack_instr[];
  riscv_reg_t              saved_regs[];
  rand riscv_instr_base    branch_instr;
  rand bit                 enable_branch;
  string                   push_start_label;

  `uvm_object_utils(riscv_push_stack_instr)

  function new(string name = "");
    super.new(name);
    branch_instr = riscv_instr_base::type_id::create("branch_instr");
  endfunction

  function void init();
    // Save RA, T0 and all reserved loop regs
    saved_regs = {RA, T0, cfg.loop_regs};
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
                                   instr_name == ADDI; rd == SP; rs1 == SP;
                                   imm == (~stack_len + 1);)
    push_stack_instr[0].imm_str = $sformatf("-%0d", stack_len);
    foreach(saved_regs[i]) begin
      if(XLEN == 32) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[i+1],
          instr_name == SW; rs2 == saved_regs[i]; rs1 == SP; imm == 4 * (i+1);)
      end else begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[i+1],
          instr_name == SD; rs2 == saved_regs[i]; rs1 == SP; imm == 8 * (i+1);)
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
      `DV_CHECK_RANDOMIZE_WITH_FATAL(branch_instr,
                                     category == BRANCH;)
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
          instr_name == LW; rd == saved_regs[i]; rs1 == SP; imm == 4 * (i+1);)
      end else begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[i],
          instr_name == LD; rd == saved_regs[i]; rs1 == SP; imm == 8 * (i+1);)
      end
      pop_stack_instr[i].process_load_store = 0;
    end
    // addi sp,sp,imm
    `DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[num_of_reg_to_save],
                                   instr_name == ADDI; rd == SP; rs1 == SP; imm == stack_len;)
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

  virtual function void gen_instr(bit no_branch = 1'b0,
                                  bit no_load_store = 1'b1,
                                  bit enable_hint_instr = 1'b0);
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
    instr_list.rand_mode(0);
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

