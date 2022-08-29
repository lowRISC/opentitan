/*
 * Copyright 2019 Google LLC
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

module riscv.gen.riscv_amo_instr_lib;


import riscv.gen.riscv_instr_pkg: riscv_reg_t, riscv_pseudo_instr_name_t,
  riscv_instr_name_t, riscv_instr_group_t, riscv_instr_category_t;
import riscv.gen.target: supported_isa, XLEN;
import riscv.gen.riscv_directed_instr_lib: riscv_mem_access_stream;
import riscv.gen.riscv_load_store_instr_lib: riscv_vector_load_store_instr_stream;
import riscv.gen.riscv_pseudo_instr: riscv_pseudo_instr;
import riscv.gen.isa.riscv_instr: riscv_instr;

import std.format: format;
import std.algorithm: canFind;

import esdl.rand: constraint, rand, randomize_with;
import esdl.base.rand: urandom;

import uvm;

class riscv_amo_base_instr_stream : riscv_mem_access_stream
{
  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  @rand uint            num_amo;
  @rand uint            num_mixed_instr;
  @rand int[]           offset;
  @rand riscv_reg_t[]   rs1_reg;
  @rand int             num_of_rs1_reg;
  uint                  data_page_id;
  uint                  max_offset;

  // User can specify a small group of available registers to generate various hazard condition
  @rand riscv_reg_t[] avail_regs;

  constraint! q{
    num_of_rs1_reg == 1;
  } num_of_rs1_reg_c;

  constraint! q{
    // solve num_of_rs1_reg before rs1_reg;
    rs1_reg.length == num_of_rs1_reg;
    offset.length == num_of_rs1_reg;
    foreach (rreg; rs1_reg) {
      rreg !inside [cfg.reserved_regs, reserved_rd, riscv_reg_t.ZERO];
    }
    unique [rs1_reg];
  } rs1_c;

  constraint! q{
    foreach (offs; offset) {
      offs inside [0..max_offset];
    }
  } addr_range_c;

  constraint! q{
    foreach (offs; offset) {
      if (XLEN == 32) {
        offs % 4 == 0;
      } else {
        offs % 8 == 0;
      }
    }
  } aligned_amo_c;


  //  `uvm_object_utils(riscv_amo_base_instr_stream)
  //  `uvm_object_new

  override void pre_randomize() {
    data_page = cfg.amo_region;
    max_data_page_id = cast(int)data_page.length;
    assert (max_data_page_id != 0);
    data_page_id = urandom(0, max_data_page_id);
    max_offset = data_page[data_page_id].size_in_bytes;
  }

  // Use "la" instruction to initialize the offset regiseter
  void init_offset_reg() {
    import std.conv: to;
    foreach (i, rreg; rs1_reg) {
      riscv_pseudo_instr la_instr;
      la_instr = riscv_pseudo_instr.type_id.create("la_instr");
      la_instr.pseudo_instr_name = riscv_pseudo_instr_name_t.LA;
      la_instr.rd = rreg;
      la_instr.imm_str = format("%0s+%0d", cfg.amo_region[data_page_id], offset[i]);
      append_instr(la_instr);
    }
  }

  override void post_randomize() {
    gen_amo_instr();
    reserved_rd ~= rs1_reg;
    add_mixed_instr(num_mixed_instr);
    init_offset_reg();
    super.post_randomize();
  }

  // AMO instruction generation
  void gen_amo_instr() { }

}

// A pair of LR/SC instruction
class riscv_lr_sc_instr_stream : riscv_amo_base_instr_stream
{
  mixin uvm_object_utils;
  this(string name = "") {
    super(name);
  }


  riscv_instr lr_instr;
  riscv_instr sc_instr;

  constraint! q{
    num_amo == 1;
    num_mixed_instr inside [0..16]; // [0:15]
  } legal_c ;


  override void gen_amo_instr() {
    riscv_instr_name_t[] allowed_lr_instr;
    riscv_instr_name_t[] allowed_sc_instr;
    if (canFind (supported_isa , riscv_instr_group_t.RV32A)) {
      allowed_lr_instr = [riscv_instr_name_t.LR_W];
      allowed_sc_instr = [riscv_instr_name_t.SC_W];
    }
    if (canFind (supported_isa, riscv_instr_group_t.RV64A)) {
      allowed_lr_instr ~= riscv_instr_name_t.LR_D;
      allowed_sc_instr ~= riscv_instr_name_t.SC_D;
    }

    lr_instr = cfg.instr_registry.get_rand_instr(allowed_lr_instr);
    sc_instr = cfg.instr_registry.get_rand_instr(allowed_sc_instr);

    lr_instr.randomize_with! q{
      rs1 == $0;
      if ($1.length > 0) {
        rd !inside [$1];
      }
      if ($2.length > 0) {
        rd !inside [$2];
      }
      rd != $0;
    } (rs1_reg[0], reserved_rd, cfg.reserved_regs);
    sc_instr.randomize_with! q{
      rs1 == $0;
      if ($1.length > 0) {
	rd !inside [$1];
      }
      if ($2.length > 0) {
	rd !inside [$2];
      }
      rd != $0;
    } (rs1_reg[0], reserved_rd, cfg.reserved_regs);
    append_instr(lr_instr);
    append_instr(sc_instr);
  }

  // section 8.3 Eventual Success of Store-Conditional Instructions
  // An LR/SC sequence begins with an LR instruction and ends with an SC instruction.
  // The dynamic code executed between the LR and SC instructions can only contain
  // instructions from the base “I” instruction set, excluding loads, stores, backward
  // jumps, taken backward branches, JALR, FENCE, and SYSTEM instructions. If the “C”
  // extension is supported, then compressed forms of the aforementioned “I” instructions
  // are also permitted.
  override void add_mixed_instr(int instr_cnt) {
    riscv_instr instr;
    int i;
    setup_allowed_instr(true, true);
    //setup_allowed_instr(.no_branch(1), .no_load_store(1));
    while (i < instr_cnt) {
      instr = riscv_instr.type_id.create("instr");
      randomize_instr(instr, false, false, [riscv_instr_group_t.RV32I, riscv_instr_group_t.RV32C]);
      if (! instr.category.inside(riscv_instr_category_t.SYNCH,
				  riscv_instr_category_t.SYSTEM)) {
        insert_instr(instr);
        i++;
      }
    }
  }

}

class riscv_amo_instr_stream: riscv_amo_base_instr_stream
{

  riscv_instr[] amo_instr;

  constraint! q{
    solve num_amo before num_mixed_instr;
    num_amo inside [1..11];
    num_mixed_instr inside [0..num_amo+1];
  } reasonable_c;

  constraint! q{
    solve num_amo before num_of_rs1_reg;
    num_of_rs1_reg inside [1..num_amo+1];
    num_of_rs1_reg < 5;
  } num_of_rs1_reg_c;

  mixin uvm_object_utils;
  this(string name = "") {
    super(name);
  }

  override void gen_amo_instr() {
    amo_instr.length = num_amo;
    foreach (i, ref instr; amo_instr) {
      instr = cfg.instr_registry.get_rand_instr([riscv_instr_category_t.AMO]);
      amo_instr[i].randomize_with! q{
        if ($0.length > 0) {
          rd !inside [$0];
        }
        if ($1.length > 0) {
          rd !inside [$1];
        }
        rs1 inside [$2];
        rd !inside [$2];
      } (reserved_rd, cfg.reserved_regs, rs1_reg);
      append_instr(instr);
    }
  }
}

class riscv_vector_amo_instr_stream: riscv_vector_load_store_instr_stream
{

  constraint! q{
    // AMO operation uses indexed address mode
    address_mode == address_mode_e.INDEXED;
  } amo_address_mode_c;

  mixin uvm_object_utils;
  this(string name = "") {
    super(name);
  }

  void add_element_vec_load_stores() {
    allowed_instr = [riscv_instr_name_t.VAMOSWAPE_V, riscv_instr_name_t.VAMOADDE_V,
		     riscv_instr_name_t.VAMOXORE_V,  riscv_instr_name_t.VAMOANDE_V,
		     riscv_instr_name_t.VAMOORE_V,   riscv_instr_name_t.VAMOMINE_V,
		     riscv_instr_name_t.VAMOMAXE_V,  riscv_instr_name_t.VAMOMINUE_V,
		     riscv_instr_name_t.VAMOMAXUE_V] ~ allowed_instr;
  }

}
