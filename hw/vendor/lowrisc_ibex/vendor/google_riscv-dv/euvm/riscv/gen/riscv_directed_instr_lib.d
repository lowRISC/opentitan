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

// Base class for directed instruction stream

module riscv.gen.riscv_directed_instr_lib;

import riscv.gen.riscv_instr_pkg: mem_region_t, riscv_reg_t, riscv_instr_name_t,
  riscv_pseudo_instr_name_t, hart_prefix, riscv_instr_category_t, riscv_instr_group_t;
import riscv.gen.target: XLEN;
import riscv.gen.isa.riscv_instr: riscv_instr;
import riscv.gen.riscv_pseudo_instr: riscv_pseudo_instr;
import riscv.gen.riscv_instr_stream: riscv_rand_instr_stream;
import std.format: format;

import std.algorithm: canFind;

import esdl.rand: rand, constraint, randomize_with, randomize;
import esdl.base.rand: urandom, shuffle;
import esdl.data.bvec: ubvec, toubvec;
import uvm;

class riscv_directed_instr_stream: riscv_rand_instr_stream
{

  mixin uvm_object_utils;

  //`uvm_object_utils(riscv_directed_instr_stream)

  string label;

  this(string name = "") {
    super(name);
  }

  void post_randomize() {
    foreach (instr; instr_list) {
      instr.has_label = false;
      instr.atomic = true;
    }
    instr_list[0].comment = format("Start %0s", get_name());
    instr_list[$-1].comment = format("End %0s", get_name());
    if(label!= "") {
      instr_list[0].label = label;
      instr_list[0].has_label = true;
    }
  }

}

// Base class for memory access stream
class riscv_mem_access_stream : riscv_directed_instr_stream
{

  mixin uvm_object_utils;

  int               max_data_page_id;
  bool              load_store_shared_memory;
  mem_region_t[]    data_page;


  this(string name = "") {
    super(name);
  }


  void pre_randomize() {
    if (load_store_shared_memory) {
      data_page = cfg.amo_region;
    }
    else if(kernel_mode) {
      data_page = cfg.s_mem_region;
    }
    else {
      data_page = cfg.mem_region;
    }
    max_data_page_id = cast(int) data_page.length;
  }

  // Use "la" instruction to initialize the base regiseter
  void add_rs1_init_la_instr(riscv_reg_t gpr, int id, int base = 0) {
    riscv_pseudo_instr la_instr;
    la_instr = riscv_pseudo_instr.type_id.create("la_instr");
    la_instr.pseudo_instr_name = riscv_pseudo_instr_name_t.LA;
    la_instr.rd = gpr;
    if (load_store_shared_memory) {
      la_instr.imm_str = format("%0s+%0d", cfg.amo_region[id].name, base);

    }
    else if(kernel_mode) {
      la_instr.imm_str = format("%0s%0s+%0d",
				hart_prefix(hart), cfg.s_mem_region[id].name, base);
    }
    else {
      la_instr.imm_str = format("%0s%0s+%0d",
				hart_prefix(hart), cfg.mem_region[id].name, base);
    }
    prepend_instr(la_instr);
  }

  // Insert some other instructions to mix with mem_access instruction
  void add_mixed_instr(int instr_cnt) {
    riscv_instr      instr;
    setup_allowed_instr(1, 1);
    for (int i = 0; i < instr_cnt; i ++) {
      instr = riscv_instr.type_id.create("instr");
      randomize_instr(instr);
      insert_instr(instr);
    }
  }

}

// Jump instruction (JAL, JALR)
// la rd0, jump_tagert_label
// addi rd1, offset, rd0
// jalr rd, offset, rd1
// For JAL, restore the stack before doing the jump
class riscv_jump_instr: riscv_directed_instr_stream
{
  riscv_instr          jump;
  riscv_instr          addi;
  riscv_pseudo_instr   la;
  riscv_instr          branch;
  @rand riscv_reg_t    gpr;
  @rand int            imm;
  @rand bool           enable_branch;
  @rand int            mixed_instr_cnt;
  riscv_instr[]        stack_exit_instr;
  string               target_program_label;
  int                  idx;
  bool                 use_jalr;

  constraint! q{
    gpr !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
    imm inside [-1023:1023];
    mixed_instr_cnt inside [5:10];
    if (jump.instr_name inside [ riscv_instr_name_t.C_JR,  riscv_instr_name_t.C_JALR]) {
      imm == 0;
    }
  }  instr_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
    la = riscv_pseudo_instr.type_id.create("la");
  }

  void pre_randomize() {
    if (use_jalr) {
      jump = cfg.instr_registry.get_instr(riscv_instr_name_t.JALR);
    }
    else if (cfg.disable_compressed_instr || (cfg.ra != riscv_reg_t.RA)) {
      jump = cfg.instr_registry.get_rand_instr([riscv_instr_name_t.JAL, riscv_instr_name_t.JALR]);
    }
    else {
      jump = cfg.instr_registry.get_rand_instr([riscv_instr_name_t.JAL, riscv_instr_name_t.JALR,
						riscv_instr_name_t.C_JALR]);
    }
    addi = cfg.instr_registry.get_instr(riscv_instr_name_t.ADDI);
    branch = cfg.instr_registry.get_rand_instr([riscv_instr_name_t.BEQ, riscv_instr_name_t.BNE,
						riscv_instr_name_t.BLT, riscv_instr_name_t.BGE,
						riscv_instr_name_t.BLTU, riscv_instr_name_t.BGEU]);
  }

  override void post_randomize() {
    riscv_instr[] instr;
    jump.randomize_with! q{
      if (has_rd == true) {
        rd == $0;
      }
      if (has_rs1 == true) {
        rs1 == $1;
      }
    } (cfg.ra, gpr);
    //DV_CHECK_RANDOMIZE_WITH_FATAL(addi, rs1 == gpr; rd == gpr;)
    addi.randomize_with! q{ rs1 == $0; rd == $0; } (gpr);
    //DV_CHECK_RANDOMIZE_FATAL(branch)
    branch.randomize();
    la.pseudo_instr_name = riscv_pseudo_instr_name_t.LA;
    la.imm_str = target_program_label;
    la.rd = gpr;
    // Generate some random instructions to mix with jump instructions
    reserved_rd = [gpr];
    initialize_instr_list(mixed_instr_cnt);
    gen_instr(true);
    if (jump.instr_name.inside(riscv_instr_name_t.JALR, riscv_instr_name_t.C_JALR)) {
      // JALR is expected to set lsb to 0
      int offset = urandom!q{[]}(0, 1);
      addi.imm_str = format("%0d", imm + offset);
    }
    else {
      addi.imm_str = format("%0d", imm);
    }
    if (cfg.enable_misaligned_instr) {
      // Jump to a misaligned address
      jump.imm_str = format("%0d", -imm + 2);
    }
    else {
      jump.imm_str = format("%0d", -imm);
    }
    // The branch instruction is always inserted right before the jump instruction to avoid
    // skipping other required instructions like restore stack, load jump base etc.
    // The purse of adding the branch instruction here is to cover branch -> jump scenario.
    if (enable_branch) instr = [branch];
    // Restore stack before unconditional jump
    if ((jump.rd == riscv_reg_t.ZERO) || (jump.instr_name == riscv_instr_name_t.C_JR)) {
      instr = stack_exit_instr ~ instr;
    }
    if (jump.instr_name == riscv_instr_name_t.JAL) {
      jump.imm_str = target_program_label;
    }
    else {
      instr = [la, addi] ~ instr;
    }
    mix_instr_stream(instr);
    append_instr(jump);
    foreach (linstr; instr_list) {
      linstr.has_label = false;
      linstr.atomic = true;
    }
    jump.has_label = true;
    jump.label = format("%0s_j%0d", label, idx);
    jump.comment = format("jump %0s -> %0s", label, target_program_label);
    branch.imm_str = jump.label;
    branch.comment = "branch to jump instr";
    branch.branch_assigned = true;
  }
}

// Stress back to back jump instruction
class riscv_jal_instr : riscv_rand_instr_stream
{
  riscv_instr[]        jump;
  riscv_instr          jump_start;
  riscv_instr          jump_end;
  @rand uint           num_of_jump_instr;
  riscv_instr_name_t[] jal;

  constraint!  q{
    num_of_jump_instr inside [10:30];
  } instr_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  void post_randomize() {
    int[]  order;
    order.length  = num_of_jump_instr;
    jump.length  = num_of_jump_instr;
    foreach (i, ref  ord; order) {
      ord = cast(int) i;
    }
    order.shuffle();
    setup_allowed_instr(1, 1);
    jal = [riscv_instr_name_t.JAL];
    if (!cfg.disable_compressed_instr) {
      jal ~= riscv_instr_name_t.C_J;
      if (XLEN == 32) {
        jal ~= riscv_instr_name_t.C_JAL;
      }
    }
    // First instruction
    jump_start = cfg.instr_registry.get_instr(riscv_instr_name_t.JAL);
    //`DV_CHECK_RANDOMIZE_WITH_FATAL(jump_start, rd == cfg.ra;)
    jump_start.randomize_with! q{rd == $0;} (cfg.ra);
    jump_start.imm_str = format("%0df", order[0]);
    jump_start.label = label;
    // Last instruction
    randomize_instr(jump_end);
    jump_end.label = format("%0d", num_of_jump_instr);
    foreach (i, ref jj ; jump) {
      jj = cfg.instr_registry.get_rand_instr(jal);
      //DV_CHECK_RANDOMIZE_WITH_FATAL(jump[i],
      // Giving randomization error
      jj.randomize_with! q{
	if (has_rd == true ) {
	  rd dist [riscv_reg_t.RA := 5, riscv_reg_t.T1 := 2, riscv_reg_t.SP..riscv_reg_t.T0 :/ 1, riscv_reg_t.T2..riscv_reg_t.T6 :/ 2];
	  rd !inside [$0];
	}
      } (cfg.reserved_regs);
      jj.label = format("%0d", i);
    }
    foreach (i, rr; order) {
      if (i == num_of_jump_instr - 1) {
	jump[rr].imm_str = format("%0df", num_of_jump_instr);
      }
      else {
	if (order[i+1] > rr) {
          jump[rr].imm_str = format("%0df", order[i+1]);
	}
	else {
          jump[rr].imm_str = format("%0db", order[i+1]);
	}
      }
    }

    instr_list = jump_start ~ jump ~ jump_end;
    foreach (instr; instr_list) {
      instr.has_label = true;
      instr.atomic = true;
    }
  }
}

// Push stack instruction stream
class riscv_push_stack_instr : riscv_rand_instr_stream
{
  int                      stack_len;
  int                      num_of_reg_to_save;
  int                      num_of_redudant_instr;
  riscv_instr[]            push_stack_instr;
  riscv_reg_t[]            saved_regs;
  riscv_instr              branch_instr;
  @rand bool               enable_branch;
  string                   push_start_label;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  void init() {
    // Save RA, T0
    reserved_rd = [cfg.ra];
    saved_regs = [cfg.ra];
    num_of_reg_to_save = cast(int) saved_regs.length;
    if(num_of_reg_to_save * (XLEN/8) > stack_len) {
      uvm_fatal(get_full_name(), format("stack len [%0d] is not enough to store %d regs",
					stack_len, num_of_reg_to_save));
    }
    num_of_redudant_instr = urandom!q{[]}(3,10);
    initialize_instr_list(num_of_redudant_instr);
  }

  void gen_push_stack_instr(int stack_len, bool allow_branch = true) {
    this.stack_len = stack_len;
    init();
    gen_instr(true);
    push_stack_instr.length = num_of_reg_to_save+1;
    foreach( i, ref sinstr; push_stack_instr) {
      sinstr = riscv_instr.type_id.create(format("push_stack_instr_%0d", i));
    }
    // addi sp,sp,-imm
    push_stack_instr[0] = cfg.instr_registry.get_instr(riscv_instr_name_t.ADDI);
    //DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[0],
    push_stack_instr[0].randomize_with! q{ rd == $0; rs1 == $0;
      imm == $1;} (cfg.sp, ~stack_len + 1);
    push_stack_instr[0].imm_str = format("-%0d", stack_len);
    foreach (i, sreg;  saved_regs) {
      if (XLEN == 32) {
        push_stack_instr[i+1] = cfg.instr_registry.get_instr(riscv_instr_name_t.SW);
	//     `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[i+1],
	push_stack_instr[i+1].randomize_with! q{
	  rs2 == $0 ; rs1 == $1 ; imm == 4 * ($2+1);
	} (sreg, cfg.sp, i);
      }
      else {
        push_stack_instr[i+1] = cfg.instr_registry.get_instr(riscv_instr_name_t.SD);
	//     `DV_CHECK_RANDOMIZE_WITH_FATAL(push_stack_instr[i+1],
	push_stack_instr[i+1].randomize_with! q{
	  instr_name == riscv_instr_name_t.SD; rs2 == $0 ; rs1 == $1 ; imm == 8 * ($2+1);
	} (sreg, cfg.sp, i);
      }
      push_stack_instr[i+1].process_load_store = false;
    }
    if (allow_branch) {
      //DV_CHECK_STD_RANDOMIZE_FATAL(enable_branch)
      enable_branch = urandom!bool();
    }
    else {
      enable_branch = false;
    }
    if (enable_branch) {
      branch_instr = cfg.instr_registry.get_rand_instr([riscv_instr_category_t.BRANCH]);
      // `DV_CHECK_RANDOMIZE_FATAL(branch_instr)
      branch_instr.randomize();
      branch_instr.imm_str = push_start_label;
      branch_instr.branch_assigned = true;
      push_stack_instr[0].label = push_start_label;
      push_stack_instr[0].has_label = true;
      push_stack_instr = [branch_instr]  ~  push_stack_instr;
    }
    mix_instr_stream(push_stack_instr);
    foreach (i, ref instr; instr_list) {
      instr.atomic = true;
      if (instr.label == "")
        instr.has_label =false;
    }
  }

}

// Pop stack instruction stream
class riscv_pop_stack_instr: riscv_rand_instr_stream
{

  int            stack_len;
  int            num_of_reg_to_save;
  int            num_of_redudant_instr;
  riscv_instr[]  pop_stack_instr;
  riscv_reg_t[]  saved_regs;


  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  //uvm_object_utils(riscv_pop_stack_instr)

  void init() {
    reserved_rd = [cfg.ra];
    num_of_reg_to_save = cast(int) saved_regs.length;
    if(num_of_reg_to_save * 4 > stack_len) {
      uvm_fatal(get_full_name(), format("stack len [%0d] is not enough to store %d regs",
					stack_len, num_of_reg_to_save));
    }
    num_of_redudant_instr = urandom!q{[]}(3,10);
    initialize_instr_list(num_of_redudant_instr);
  }

  void gen_pop_stack_instr(int stack_len, riscv_reg_t[] saved_regs) {
    this.stack_len = stack_len;
    this.saved_regs = saved_regs;
    init();
    gen_instr(true);
    pop_stack_instr.length  = num_of_reg_to_save+1;
    foreach (i, ref psinstr;  pop_stack_instr) {
      psinstr = riscv_instr.type_id.create(format("pop_stack_instr_%0d", i));
    }
    foreach (i, ref sreg; saved_regs) {
      if (XLEN == 32) {
        pop_stack_instr[i] = cfg.instr_registry.get_instr(riscv_instr_name_t.LW);
        //DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[i],
	pop_stack_instr[i].randomize_with! q{
	  rd == $0; rs1 == $1; imm == 4 * ($2+1);
	} (sreg, cfg.sp, i);
      }
      else {
        pop_stack_instr[i] = cfg.instr_registry.get_instr(riscv_instr_name_t.LD);
        //DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[i],
	pop_stack_instr[i].randomize_with! q{
	  rd == $0; rs1 == $1; imm == 8 * ($2+1);
	} (sreg, cfg.sp, i);
      }
      pop_stack_instr[i].process_load_store = false;
    }
    // addi sp,sp,imm
    pop_stack_instr[num_of_reg_to_save] = cfg.instr_registry.get_instr(riscv_instr_name_t.ADDI);
    //DV_CHECK_RANDOMIZE_WITH_FATAL(pop_stack_instr[num_of_reg_to_save],
    pop_stack_instr[num_of_reg_to_save].randomize_with! q{
      rd == $0; rs1 == $0; imm == $1;
    } ( cfg.sp, stack_len);
    pop_stack_instr[num_of_reg_to_save].imm_str = format("%0d", stack_len);
    mix_instr_stream(pop_stack_instr);
    foreach (instr; instr_list) {
      instr.atomic = true;
      instr.has_label = false;
    }
  }

}

// Strees the numeric corner cases of integer arithmetic operations
class riscv_int_numeric_corner_stream: riscv_directed_instr_stream
{
  enum int_numeric_e {
    NormalValue,
    Zero,
    AllOne,
    NegativeMax
  }

  uint                  num_of_avail_regs = 10;
  @rand uint            num_of_instr;
  @rand ubvec!XLEN[]    init_val; // becasue of compile error it has been commented.
  @rand int_numeric_e[] init_val_type;
  riscv_pseudo_instr[]  init_instr;

  constraint! q{
    //solve init_val_type before init_val;
    init_val_type.length == num_of_avail_regs;
    init_val.length == num_of_avail_regs;
    num_of_instr inside [15..31];
  }  init_val_c ;

  constraint! q{
    unique [avail_regs];
    foreach (areg; avail_regs) {
      areg !inside [cfg.reserved_regs];
      areg != riscv_reg_t.ZERO;
    }
  }  avail_regs_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  void pre_randomize() {
    avail_regs.length = num_of_avail_regs;
    // super.pre_randomize();
  }

  override  void post_randomize() {
    init_instr.length = num_of_avail_regs;
    foreach (i, ref ivtype; init_val_type) {
      if (ivtype == int_numeric_e.Zero) {
        init_val[i] = toubvec!XLEN(0);
      }
      else if (ivtype == int_numeric_e.AllOne) {
        init_val[i] = toubvec!XLEN(-1);
      }
      else if (ivtype == int_numeric_e.NegativeMax) {
        init_val[i] = toubvec!XLEN(1UL << (XLEN-1));
      }
      init_instr[i] = new riscv_pseudo_instr;
      init_instr[i].rd = avail_regs[i];
      init_instr[i].pseudo_instr_name = riscv_pseudo_instr_name_t.LI;
      init_instr[i].imm_str = format("0x%0x", init_val[i]);
      append_instr(init_instr[i]);
    }
    for (int i = 0; i < num_of_instr; i++) {
      riscv_instr instr =
	cfg.instr_registry.get_rand_instr([riscv_instr_category_t.ARITHMETIC],
					  [riscv_instr_group_t.RV32C, riscv_instr_group_t.RV64C,
					   riscv_instr_group_t.RV32F , riscv_instr_group_t.RV64F,
					   riscv_instr_group_t.RV32D, riscv_instr_group_t.RV64D]);
      randomize_gpr(instr);
      append_instr(instr);
    }
    super.post_randomize();
  }

}
