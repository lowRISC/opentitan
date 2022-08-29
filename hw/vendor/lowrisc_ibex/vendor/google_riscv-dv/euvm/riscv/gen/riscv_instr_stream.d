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

// Base class for RISC-V instruction stream
// A instruction stream here is a  queue of RISC-V basic instructions.
// This class also provides some functions to manipulate the instruction stream, like insert a new
// instruction, mix two instruction streams etc.

module riscv.gen.riscv_instr_stream;

import riscv.gen.riscv_instr_pkg: riscv_instr_name_t, riscv_reg_t,
  riscv_instr_category_t, riscv_instr_group_t, riscv_vreg_t,
  riscv_pseudo_instr_name_t, va_variant_t;
import riscv.gen.isa.riscv_instr: riscv_instr;
import riscv.gen.riscv_pseudo_instr: riscv_pseudo_instr;
// import riscv.gen.riscv_instr_registry: riscv_instr_registry;
import riscv.gen.isa.riscv_vector_instr: riscv_vector_instr;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import riscv.gen.target: XLEN;

import std.format: format;
import std.algorithm: canFind, sort;

import esdl.rand: rand, constraint, randomize, randomize_with;
import esdl.base.rand: urandom;
import esdl.data.queue: Queue;
import esdl.data.bvec: ubvec;

import uvm;

class riscv_instr_stream: uvm_object
{
  mixin uvm_object_utils;

  Queue!riscv_instr        instr_list;
  uint                     instr_cnt;
  string                   label = "";
  // User can specify a small group of available registers to generate various hazard condition
  @rand riscv_reg_t[]      avail_regs;
  // Some additional reserved registers that should not be used as rd register
  // by this instruction stream
  riscv_reg_t[]            reserved_rd;
  int                      hart;

  // used when we mixin directed instructions into the prog instr_list
  uint next_stream;

  // riscv_instr_registry     registry;

  this(string name = "riscv_instr_stream") {
    super(name);
  }

  // Initialize the instruction stream, create each instruction instance

  void initialize_instr_list(uint instr_cnt) {
    instr_list.length = 0;
    this.instr_cnt = instr_cnt;
    create_instr_instance();
  }

  void create_instr_instance() {
    riscv_instr instr;
    for (int i = 0; i < instr_cnt; i++) {
      instr = riscv_instr.type_id.create(format("instr_%0d", i));
      append_instr(instr);
    }
  }

  // Insert an instruction to the existing instruction stream at the given index
  // When index is -1, the instruction is injected at a random location
  void insert_instr(riscv_instr instr, int idx = -1) {
    int current_instr_cnt = cast(int) instr_list.length;
    if (current_instr_cnt == 0) {
      idx = 0;
    }
    else if (idx == -1) {
      idx = cast(int) urandom(0, current_instr_cnt);
      while (instr_list[idx].atomic) {
	idx += 1;
	if (idx == current_instr_cnt - 1) {
	  instr_list ~= instr;
	  return;
	}
      }
    }
    else if ((idx > current_instr_cnt) || (idx < 0)) {
      uvm_error(get_full_name() ,
		format("Cannot insert instr:%0s at idx %0d",
		       instr.convert2asm(), idx));
    }
    instr_list.insert(idx, instr);
  }

  void insert_instr_map(Queue!riscv_instr new_instr, int idx = -1, bool replace = false) {
    assert (replace == false);
  }

  // Insert an instruction to the existing instruction stream at the given index
  // When index is -1, the instruction is injected at a random location
  // When replace is 1, the original instruction at the inserted position will be replaced
  void insert_instr_stream(Queue!riscv_instr new_instr, int idx = -1, bool replace = false) {
    int current_instr_cnt = cast(int) instr_list.length;
    int new_instr_cnt = cast(int) new_instr.length;
    if (current_instr_cnt == 0) {
      instr_list ~= new_instr;
      return;
    }
    if (idx == -1) {
      idx = cast(int) urandom(0, current_instr_cnt);
      for (int i=0; i < 10 ; i++) {
	if (instr_list[idx].atomic) break;
	idx = cast(int) urandom(0, current_instr_cnt);
      }
      if (instr_list[idx].atomic) {
	foreach (k, instr; instr_list) {
	  if (! instr.atomic) {
	    idx = cast(int) k;
	    break;
	  }
	}
	if (instr_list[idx].atomic) {
	  uvm_fatal(get_full_name, format("Cannot inject the instruction"));
	}
      }
    }
    else if((idx > current_instr_cnt) || (idx < 0)) {
      uvm_error(get_full_name(), format("Cannot insert instr stream at idx %0d", idx));
    }
    //When replace is 1, the original instruction at this index will be removed. The label of the
    //original instruction will be copied to the head of inserted instruction stream.
    if (replace) {
      new_instr[0].label = instr_list[idx].label;
      new_instr[0].has_label = instr_list[idx].has_label;
      foreach (i, instr; new_instr) {
	instr_list[i+idx] = instr;
      }
    }
    else {
      if (idx == 0) {
	instr_list.pushFront(new_instr[]);
      }
      else {
        instr_list.insert(idx, new_instr[]);
      }
    }
  }

  void insert_instr_stream(riscv_instr[] new_instr, int idx = -1, bool replace = false) {
    int current_instr_cnt = cast(int) instr_list.length;
    int new_instr_cnt = cast(int) new_instr.length;
    if (current_instr_cnt == 0) {
      instr_list ~= new_instr;
      return;
    }
    if (idx == -1) {
      idx = cast(int) urandom(0, current_instr_cnt);
      for (int i=0; i < 10 ; i++) {
	if (instr_list[idx].atomic) break;
	idx = cast(int) urandom(0, current_instr_cnt);
      }
      if (instr_list[idx].atomic) {
	foreach (k, instr; instr_list) {
	  if (! instr.atomic) {
	    idx = cast(int) k;
	    break;
	  }
	}
	if (instr_list[idx].atomic) {
	  uvm_fatal(get_full_name, format("Cannot inject the instruction"));
	}
      }
    }
    else if((idx > current_instr_cnt) || (idx < 0)) {
      uvm_error(get_full_name(), format("Cannot insert instr stream at idx %0d", idx));
    }
    //When replace is 1, the original instruction at this index will be removed. The label of the
    //original instruction will be copied to the head of inserted instruction stream.
    if (replace) {
      new_instr[0].label = instr_list[idx].label;
      new_instr[0].has_label = instr_list[idx].has_label;
      if (idx == 0) {
	instr_list.removeFront();
	instr_list.pushFront(new_instr);
      }
      else {
	instr_list.remove(idx);
	instr_list.insert(idx, new_instr);
      }
     }
    else {
      if (idx == 0) {
	instr_list.pushFront(new_instr);
      }
      else {
        instr_list.insert(idx, new_instr);
      }
    }
  }

  void append_instr(riscv_instr instr) {
    instr_list ~= instr;
  }

  void prepend_instr(riscv_instr instr) {
    instr_list.pushFront(instr);
  }

  void append_instr_list(Queue!riscv_instr instr) {
    instr_list ~= instr[];
  }

  void prepend_instr_list(Queue!riscv_instr instr) {
    instr_list.pushFront(instr[]);
  }

  // Mix the input instruction stream with the original instruction, the instruction order is
  // preserved. When 'contained' is set, the original instruction stream will be inside the
  // new instruction stream with the first and last instruction from the input instruction stream.
  void mix_instr_stream(riscv_instr[] new_instr, bool contained = false) {
    int current_instr_cnt = cast(int) instr_list.length;
    int[] insert_instr_position;
    int new_instr_cnt = cast(int) new_instr.length;
    insert_instr_position.length = new_instr_cnt;
    foreach (ref position; insert_instr_position) {
      position = urandom(0, current_instr_cnt);
    }
    if (insert_instr_position.length > 0) {
      insert_instr_position.sort();
    }
    if (contained) {
      insert_instr_position[0] = 0;
      if (new_instr_cnt > 1) {
	insert_instr_position[new_instr_cnt-1] = current_instr_cnt-1;
      }
    }
    foreach (k, instr; new_instr) {
      insert_instr(instr, insert_instr_position[k] + cast(int) k);
    }
  }

  void mix_instr_stream(Queue!riscv_instr new_instr, bool contained = false) {
    import std.range: enumerate;
    int current_instr_cnt = cast(int) instr_list.length;
    int[] insert_instr_position;
    int new_instr_cnt = cast(int) new_instr.length;
    insert_instr_position.length = new_instr_cnt;
    foreach (ref position; insert_instr_position) {
      position = urandom(0, current_instr_cnt+1);
    }
    if (insert_instr_position.length > 0) {
      insert_instr_position.sort();
    }
    if (contained) {
      insert_instr_position[0] = 0;
      if (new_instr_cnt > 1) {
	insert_instr_position[new_instr_cnt-1] = current_instr_cnt-1;
      }
    }
    foreach (k, instr; new_instr[].enumerate) {
      insert_instr(instr, insert_instr_position[k] + cast(int) k);
    }
  }

  override string convert2string() {
    string str;
    foreach (instr; instr_list)
      str ~= instr.convert2asm() ~ "\n";
    return str;
  }

}

// Generate a random instruction stream based on the configuration
// There are two ways to use this class to generate instruction stream
// 1. For short instruction stream, you can call randomize() directly.
// 2. For long instruction stream (>1K), randomize() all instructions together might take a long
// time for the constraint solver. In this case, you can call gen_instr to generate instructions
// one by one. The time only grows linearly with the instruction count
class riscv_rand_instr_stream: riscv_instr_stream
{
  mixin uvm_object_utils;

  riscv_instr_gen_config       cfg;
  bool                         kernel_mode;
  riscv_instr_name_t[]         allowed_instr;
  uint[riscv_instr_category_t] category_dist;

  this(string name = "riscv_rand_instr_stream") {
    super(name);
  }

  override void create_instr_instance() {
    instr_list.length = instr_cnt;
  }

  void setup_allowed_instr(bool no_branch = false, bool no_load_store = true) {
    allowed_instr = cfg.instr_registry.basic_instr;
    if (no_branch == false) {
      allowed_instr ~= cfg.instr_registry.instr_category[riscv_instr_category_t.BRANCH];
    }
    if (no_load_store == false) {
      allowed_instr ~= cfg.instr_registry.instr_category[riscv_instr_category_t.LOAD];
      allowed_instr ~= cfg.instr_registry.instr_category[riscv_instr_category_t.STORE];
    }
    setup_instruction_dist(no_branch, no_load_store);
  }

  void randomize_avail_regs() {
    import std.traits: EnumMembers;
    import std.algorithm.mutation: remove;
    import std.algorithm.searching: countUntil;
    if (avail_regs.length > 0) {
      riscv_reg_t[(EnumMembers!riscv_reg_t).length] allowed_regs = [EnumMembers!riscv_reg_t];
      riscv_reg_t[] allowed_regs_range = allowed_regs;
      // remove cfg.reserved_regs and reserved_rd
      foreach (rreg; cfg.reserved_regs) {
	ptrdiff_t loc = allowed_regs_range.countUntil(rreg);
	if (loc >= 0) allowed_regs_range.remove(loc);
      }
      foreach (rreg; reserved_rd) {
	ptrdiff_t loc = allowed_regs_range.countUntil(rreg);
	if (loc >= 0) allowed_regs_range.remove(loc);
      }
      // avail_regs[0] has to be between S0 and A5
      auto start0 = allowed_regs_range.countUntil!((a) => a >= riscv_reg_t.S0);
      auto end0 =   allowed_regs_range.countUntil!((a) => a >  riscv_reg_t.A5);
      if (end0 < 0) end0 = allowed_regs_range.length;
      if (start0 < 0 || start0 == end0) assert(false, "Cannot randomize avail_regs");
      auto loc0 =   urandom(start0, end0);
      avail_regs[0] = allowed_regs_range[loc0];
      allowed_regs_range.remove(loc0);
      // avail_regs elements have to be unique
      for (size_t n=1; n != avail_regs.length; ++n) {
	if (allowed_regs_range.length == 0) assert (false, "Cannot randomize avail_regs");
	assert(allowed_regs_range.length != 0);
	auto loc = urandom(0, allowed_regs_range.length);
	avail_regs[n] = allowed_regs_range[loc];
	allowed_regs_range.remove(loc);
      }
    }
  }

  void setup_instruction_dist(bool no_branch = false, bool no_load_store = true) {
    if (cfg.dist_control_mode) {
      category_dist = cfg.category_dist;
      if (no_branch) {
	category_dist[riscv_instr_category_t.BRANCH] = 0;
      }
      if (no_load_store) {
	category_dist[riscv_instr_category_t.LOAD] = 0;
	category_dist[riscv_instr_category_t.STORE] = 0;
      }
      uvm_info(get_full_name(), format("setup_instruction_dist: %0d", category_dist.length), UVM_LOW);
    }
  }

  void gen_instr(bool no_branch = false, bool no_load_store = true,
		 bool is_debug_program = false) {
    setup_allowed_instr(no_branch, no_load_store);
    assert (instr_list.length != 0);
    foreach (ref instr; instr_list) {
      randomize_instr(instr, is_debug_program);
    }
    // Do not allow branch instruction as the last instruction because there's no
    // forward branch target
    while (instr_list[$-1].category == riscv_instr_category_t.BRANCH) {
      instr_list.length = instr_list.length - 1;
      if (instr_list.length == 0) break;
    }
  }

  void randomize_instr(out riscv_instr instr,
		       bool is_in_debug = false,
		       bool disable_dist = false,
		       riscv_instr_group_t[] include_group = []) {
    riscv_instr_name_t[] exclude_instr;
    if (reserved_rd.canFind(riscv_reg_t.SP) || cfg.reserved_regs.canFind(riscv_reg_t.SP) ||
	(avail_regs.length > 0 && ! avail_regs.canFind(riscv_reg_t.SP))) {
      exclude_instr = [riscv_instr_name_t.C_ADDI4SPN, riscv_instr_name_t.C_ADDI16SP,
		       riscv_instr_name_t.C_LWSP, riscv_instr_name_t.C_LDSP];
    }
    // Post-process the allowed_instr and exclude_instr lists to handle
    // adding ebreak instructions to the debug rom.
    if (is_in_debug) {
      if (cfg.no_ebreak && cfg.enable_ebreak_in_debug_rom) {
        allowed_instr ~= [riscv_instr_name_t.EBREAK, riscv_instr_name_t.C_EBREAK];
      }
      else if (! cfg.no_ebreak && ! cfg.enable_ebreak_in_debug_rom) {
	exclude_instr ~= [riscv_instr_name_t.EBREAK, riscv_instr_name_t.C_EBREAK];
      }
    }
    instr = cfg.instr_registry.get_rand_instr(allowed_instr, exclude_instr, include_group);
    randomize_gpr(instr);
  }

  void randomize_gpr(riscv_instr instr) {
    assert (cfg !is null);
    instr.m_cfg = cfg;
    instr.randomize_with! q{
      if ($0.length > 0) {
        if (has_rs1) {
	  rs1 inside [$0];
	}
        if (has_rs2) {
          rs2 inside [$0];
        }
        if (has_rd) {
          rd  inside [$0];
        }
      }
      foreach (rrd; $1) {
	if (has_rd) {
	  rd != rrd;
	}
	if (instr_format == riscv_instr_format_t.CB_FORMAT) {
          rs1 != rrd;
	}
      }
      foreach (rreg; $2) {
        if (has_rd) {
          rd != rreg;
        }
        if (instr_format == riscv_instr_format_t.CB_FORMAT) {
          rs1 != rreg;
        }
      }
    } (avail_regs, reserved_rd, cfg.reserved_regs);
    // TODO: Add constraint for CSR, floating point register
  }


  riscv_instr get_init_gpr_instr(riscv_reg_t gpr, ubvec!XLEN val) {
    riscv_pseudo_instr li_instr;
    li_instr = riscv_pseudo_instr.type_id.create("li_instr");
    li_instr.randomize_with! q{
      pseudo_instr_name == riscv_pseudo_instr_name_t.LI;
      rd == $0;
    } (gpr);
    li_instr.imm_str = format("0x%0x", val);
    return li_instr;
  }

  void  add_init_vector_gpr_instr(riscv_vreg_t gpr, ubvec!XLEN val) {
    riscv_vector_instr instr
      = cast(riscv_vector_instr) cfg.instr_registry.get_instr(riscv_instr_name_t.VMV);
    instr.m_cfg = cfg;
    instr.avoid_reserved_vregs_c.constraint_mode(false);
    instr.randomize_with! q{
      va_variant == va_variant_t.VX;
      vd == $0;
      rs1 == $1;
    } (gpr, cfg.gpr[0]);
    prepend_instr(instr);
    prepend_instr(get_init_gpr_instr(cfg.gpr[0], val));
  }
}


class riscv_prog_instr_stream: riscv_rand_instr_stream
{
  mixin uvm_object_utils;

  riscv_instr_stream[] dir_instr_list;

  // used in mixin_directed_instr_list
  uint[] dir_n;

  this(string name = "riscv_prog_instr_stream") {
    super(name);
  }

  // Insert an instruction to the existing instruction stream at the given index
  // When index is -1, the instruction is injected at a random location
  // When replace is 1, the original instruction at the inserted position will be replaced
  override void insert_instr_stream(Queue!riscv_instr new_instr, int idx = -1, bool replace = false) {
    int current_instr_cnt = cast(int) instr_list.length;
    int new_instr_cnt = cast(int) new_instr.length;
    if (current_instr_cnt == 0) {
      instr_list = new_instr;
      return;
    }
    if (idx == -1) {
      idx = cast(int) urandom(0, current_instr_cnt);
      for (int i=0; i < 10 ; i++) {
	if (instr_list[idx].atomic) break;
	idx = cast(int) urandom(0, current_instr_cnt);
      }
      if (instr_list[idx].atomic) {
	foreach (k, instr; instr_list) {
	  if (! instr.atomic) {
	    idx = cast(int) k;
	    break;
	  }
	}
	if (instr_list[idx].atomic) {
	  uvm_fatal(get_full_name, format("Cannot inject the instruction"));
	}
      }
    }
    else if((idx > current_instr_cnt) || (idx < 0)) {
      uvm_error(get_full_name(), format("Cannot insert instr stream at idx %0d", idx));
    }
    //When replace is 1, the original instruction at this index will be removed. The label of the
    //original instruction will be copied to the head of inserted instruction stream.
    if (replace) {
      new_instr[0].label = instr_list[idx].label;
      new_instr[0].has_label = instr_list[idx].has_label;
      foreach (i, instr; new_instr) {
	instr_list[i+idx] = instr;
      }
    }
    else {
      if (idx == 0) {
	instr_list.pushFront(new_instr[]);
      }
      else {
        instr_list.insert(idx, new_instr[]);
      }
    }
  }

  override void insert_instr_stream(riscv_instr[] new_instr, int idx = -1, bool replace = false) {
    int current_instr_cnt = cast(int) instr_list.length;
    int new_instr_cnt = cast(int) new_instr.length;
    if (current_instr_cnt == 0) {
      instr_list ~= new_instr;
      return;
    }
    if (idx == -1) {
      idx = cast(int) urandom(0, current_instr_cnt);
      for (int i=0; i < 10 ; i++) {
	if (instr_list[idx].atomic) break;
	idx = cast(int) urandom(0, current_instr_cnt);
      }
      if (instr_list[idx].atomic) {
	foreach (k, instr; instr_list) {
	  if (! instr.atomic) {
	    idx = cast(int) k;
	    break;
	  }
	}
	if (instr_list[idx].atomic) {
	  uvm_fatal(get_full_name, format("Cannot inject the instruction"));
	}
      }
    }
    else if((idx > current_instr_cnt) || (idx < 0)) {
      uvm_error(get_full_name(), format("Cannot insert instr stream at idx %0d", idx));
    }
    //When replace is 1, the original instruction at this index will be removed. The label of the
    //original instruction will be copied to the head of inserted instruction stream.
    if (replace) {
      new_instr[0].label = instr_list[idx].label;
      new_instr[0].has_label = instr_list[idx].has_label;
      foreach (i, instr; new_instr) {
	instr_list[i+idx] = instr;
      }
     }
    else {
      if (idx == 0) {
	instr_list.pushFront(new_instr);
      }
      else {
        instr_list.insert(idx, new_instr);
      }
    }
  }

  void mixin_directed_instr_list(riscv_instr_stream[] dir_list) {
    riscv_instr[]        mixed_list;

    uint instr_count = cast(uint) instr_list.length;
    uint mixed_count = instr_count;

    dir_n.length = instr_count;

    this.dir_instr_list = dir_list;

    foreach (size_t dir_idx, dir_instr; dir_instr_list) {
      mixed_count += dir_instr.instr_list.length;
      uint rnd_idx = urandom(0, instr_count);
      uint next_dir = dir_n[rnd_idx];
      if (next_dir == 0)
	dir_n[rnd_idx] = cast(uint) (dir_idx + 1);
      else {
	uint insert_idx = cast(uint) (dir_idx + 1);
	riscv_instr_stream instr = dir_instr_list[next_dir-1];
	while (instr.next_stream != 0) {
	  if (rnd_idx % 2 == 0) { // insert at the end of linked list
	    uint next_idx = instr.next_stream;
	    instr.next_stream = insert_idx;
	    insert_idx = next_idx;
	  }
	  instr = dir_instr_list[instr.next_stream-1];
	}
	instr.next_stream = cast(uint) (insert_idx);
      }
    }

    mixed_list.length = mixed_count;

    uint n = 0;
    foreach (i, instr; instr_list) {
      uint next_dir = dir_n[i];
      while (next_dir != 0) {
	uint next = dir_instr_list[next_dir-1].next_stream;
	foreach (dinstr; dir_instr_list[next_dir-1].instr_list) {
	  mixed_list[n++] = dinstr;
	}
	next_dir = next;
      }
      mixed_list[n++] = instr;
    }
    assert (mixed_count == n);

    instr_list = mixed_list;
  }

}
