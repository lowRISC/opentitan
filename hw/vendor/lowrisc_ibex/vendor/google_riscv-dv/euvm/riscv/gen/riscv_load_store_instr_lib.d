/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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

// Base class for all load/store instruction stream

module riscv.gen.riscv_load_store_instr_lib;

import riscv.gen.isa.riscv_instr: riscv_instr;
import riscv.gen.riscv_instr_pkg: riscv_reg_t, riscv_vreg_t, riscv_instr_name_t,
  riscv_instr_group_t, riscv_instr_category_t;
import riscv.gen.target: XLEN, VLEN, supported_isa;
import riscv.gen.riscv_pseudo_instr: riscv_pseudo_instr;
import riscv.gen.isa.riscv_vector_instr: riscv_vector_instr;
import riscv.gen.riscv_directed_instr_lib: riscv_mem_access_stream;


import std.format: format;
import std.algorithm.searching: canFind, minElement, maxElement;

import esdl.rand: rand, constraint, randomize_with;
import esdl.base.rand: urandom;
import esdl.data.queue: Queue;
import esdl.data.bvec: ubvec, toubvec;

import uvm;


class riscv_load_store_base_instr_stream : riscv_mem_access_stream
{
  enum  locality_e : ubyte {
    NARROW,
    HIGH,
    MEDIUM,
    SPARSE
  }

  @rand uint            num_load_store;
  @rand uint            num_mixed_instr;
  @rand int             base;
  int[]                 offset;
  int[]                 addr;
  riscv_instr[]         load_store_instr;
  @rand uint            data_page_id;
  @rand riscv_reg_t     rs1_reg;
  @rand locality_e      locality;
  @rand uint            max_load_store_offset;
  @rand bool            use_sp_as_rs1;

  mixin uvm_object_utils;

  constraint!  q{
    solve use_sp_as_rs1 before rs1_reg;
  } sp_rnd_order_c;

  constraint! q{
    use_sp_as_rs1 dist [true := 1, false := 2];
    if (use_sp_as_rs1 == true) {
      rs1_reg == riscv_reg_t.SP;
    }
  } sp_c;

  constraint! q{
    rs1_reg !inside [cfg.reserved_regs, reserved_rd, riscv_reg_t.ZERO];
  } rs1_c ;

  constraint! q{
    solve data_page_id before max_load_store_offset;
    solve max_load_store_offset before base;
    data_page_id < max_data_page_id;
    foreach (i, page; data_page) {
      if (i == data_page_id) {
	max_load_store_offset == page.size_in_bytes;
      }
    }
    base inside [0..max_load_store_offset];
  }  addr_c;

  this(string name = "") {
    super(name);
  }

  void randomize_offset() {
    import std.algorithm: min, max;
    int offset_, addr_;
    offset.length  = num_load_store;
    addr.length = num_load_store;
    if (base < 0 || base >= max_load_store_offset)
      assert (false);
    for (int i=0; i!=num_load_store; ++i) {
      if (locality == locality_e.NARROW) {
	offset_ = urandom!q{[]}(max(-16, 0-base), min(16, max_load_store_offset - 1 - base));
      }
      else if (locality == locality_e.HIGH) {
	offset_ = urandom!q{[]}(max(-64, 0-base), min(64, max_load_store_offset - 1 - base));
      }
      else if (locality == locality_e.MEDIUM) {
	offset_ = urandom!q{[]}(max(-256, 0-base), min(256, max_load_store_offset - 1 - base));
      }
      else if (locality == locality_e.SPARSE) {
	offset_ = urandom!q{[]}(max(-2048, 0-base), min(2047, max_load_store_offset - 1 - base));
      }
      addr_ = base + offset_;
      if (addr_ < 0 || addr_ >= max_load_store_offset) assert (false);
      offset[i] = offset_;
      addr[i] = addr_;
    }
  }

  override void pre_randomize() {
    super.pre_randomize();
    if (canFind(cfg.reserved_regs, riscv_reg_t.SP) ||
	canFind(reserved_rd, riscv_reg_t.SP)) {
      use_sp_as_rs1 = false;
      rand_mode!q{use_sp_as_rs1}(false);
      sp_rnd_order_c.constraint_mode(false);
    }
  }

  override void post_randomize() {
    randomize_offset();
    // rs1 cannot be modified by other instructions
    if (!canFind(reserved_rd, rs1_reg )) {
      reserved_rd ~= rs1_reg;
    }
    gen_load_store_instr();
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);
    super.post_randomize();
  }

  // Generate each load/store instruction
  void gen_load_store_instr() {
    bool enable_compressed_load_store;
    riscv_instr instr;
    randomize_avail_regs();
    if (((rs1_reg >= riscv_reg_t.S0 && rs1_reg <= riscv_reg_t.A5) ||
	 rs1_reg == riscv_reg_t.SP) && !cfg.disable_compressed_instr) {
      enable_compressed_load_store = true;
    }
    foreach (i, a; addr) {
      // Assign the allowed load/store instructions based on address alignment
      // This is done separately rather than a constraint to improve the randomization performance
      allowed_instr = [riscv_instr_name_t.LB, riscv_instr_name_t.LBU, riscv_instr_name_t.SB];
      if (!cfg.enable_unaligned_load_store) {
        if (a % 2 == 0) {
          allowed_instr = [riscv_instr_name_t.LH, riscv_instr_name_t.LHU, riscv_instr_name_t.SH] ~
	    allowed_instr;
        }
        if (a % 4 == 0) {
          allowed_instr = [riscv_instr_name_t.LW, riscv_instr_name_t.SW] ~ allowed_instr;
          if (cfg.enable_floating_point) {
            allowed_instr = [riscv_instr_name_t.FLW, riscv_instr_name_t.FSW] ~ allowed_instr;
          }
          if ((offset[i] >= 0 && offset[i] <= 127) && (offset[i] % 4 == 0) &&
	      (canFind(supported_isa ,riscv_instr_group_t.RV32C)) &&
	      enable_compressed_load_store) {
            if (rs1_reg == riscv_reg_t.SP) {
              uvm_info(get_full_name(), "Add LWSP/SWSP to allowed instr", UVM_LOW);
              allowed_instr = [riscv_instr_name_t.C_LWSP, riscv_instr_name_t.C_SWSP];
            }
	    else {
              allowed_instr = [riscv_instr_name_t.C_LW, riscv_instr_name_t.C_SW] ~  allowed_instr;
              if (cfg.enable_floating_point && (canFind(supported_isa, riscv_instr_group_t.RV32FC ))) {
                allowed_instr = [riscv_instr_name_t.C_FLW, riscv_instr_name_t.C_FSW] ~  allowed_instr;
              }
            }
          }
        }
        if ((XLEN >= 64) && (a % 8 == 0)) {
          allowed_instr = [riscv_instr_name_t.LWU, riscv_instr_name_t.LD, riscv_instr_name_t.SD] ~
	    allowed_instr;
          if (cfg.enable_floating_point && (canFind(supported_isa, riscv_instr_group_t.RV32D ))) {
            allowed_instr = [riscv_instr_name_t.FLD, riscv_instr_name_t.FSD] ~ allowed_instr;
          }
          if ((offset[i] >= 0 && offset[i] <= 255) && (offset[i] % 8 == 0) &&
	      (canFind(supported_isa, riscv_instr_group_t.RV64C) &&
	       enable_compressed_load_store)) {
            if (rs1_reg == riscv_reg_t.SP) {
              allowed_instr = [riscv_instr_name_t.C_LDSP, riscv_instr_name_t.C_SDSP];
            }
	    else {
              allowed_instr = [riscv_instr_name_t.C_LD, riscv_instr_name_t.C_SD] ~ allowed_instr;
              if (cfg.enable_floating_point && (canFind(supported_isa, riscv_instr_group_t.RV32DC))) {
                allowed_instr = [riscv_instr_name_t.C_FLD, riscv_instr_name_t.C_FSD] ~ allowed_instr;
	      }
	    }
	  }
        }
      }
      else { // unaligned load/store
        allowed_instr = [riscv_instr_name_t.LW, riscv_instr_name_t.SW, riscv_instr_name_t.LH,
			 riscv_instr_name_t.LHU, riscv_instr_name_t.SH] ~  allowed_instr;
        // Compressed load/store still needs to be aligned
        if ((offset[i] >= 0 && offset[i] <= 127) && (offset[i] % 4 == 0) &&
            (canFind(supported_isa, riscv_instr_group_t.RV32C )) &&
            enable_compressed_load_store) {
	  if (rs1_reg == riscv_reg_t.SP) {
	    allowed_instr = [riscv_instr_name_t.C_LWSP, riscv_instr_name_t.C_SWSP];
	  }
	  else {
	    allowed_instr = [riscv_instr_name_t.C_LW, riscv_instr_name_t.C_SW] ~ allowed_instr;
	  }
        }
        if (XLEN >= 64) {
          allowed_instr = [riscv_instr_name_t.LWU, riscv_instr_name_t.LD, riscv_instr_name_t.SD] ~
	    allowed_instr;
          if ((offset[i] >= 0 && offset[i] <= 255) && (offset[i] % 8 == 0) &&
	      (canFind(supported_isa, riscv_instr_group_t.RV64C)) &&
              enable_compressed_load_store) {
	    if (rs1_reg == riscv_reg_t.SP) {
	      allowed_instr = [riscv_instr_name_t.C_LWSP, riscv_instr_name_t.C_SWSP];
	    }
	    else {
	      allowed_instr = [riscv_instr_name_t.C_LD, riscv_instr_name_t.C_SD] ~ allowed_instr;
	    }
	  }
        }
      }
      instr = cfg.instr_registry.get_load_store_instr(allowed_instr);
      instr.has_rs1 = false;
      instr.has_imm = false;
      randomize_gpr(instr);
      instr.rs1 = rs1_reg;
      instr.imm_str = format("%0d", offset[i]);  // $signed(offset[i]));
      instr.process_load_store = 0;
      append_instr(instr);
      load_store_instr ~= instr;
    }
  }

}

// A single load/store instruction
class riscv_single_load_store_instr_stream : riscv_load_store_base_instr_stream
{

  constraint! q{
    num_load_store == 1;
    num_mixed_instr < 5;
  }  legal_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

}

// Back to back load/store instructions
class riscv_load_store_stress_instr_stream : riscv_load_store_base_instr_stream
{

  uint max_instr_cnt = 30;
  uint min_instr_cnt = 10;

  constraint! q{
    num_load_store inside [min_instr_cnt:max_instr_cnt];
    num_mixed_instr == 0;
  }  legal_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

}


// Back to back load/store instructions
class riscv_load_store_shared_mem_stream : riscv_load_store_stress_instr_stream
{

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  override   void pre_randomize() {
    load_store_shared_memory = 1;
    super.pre_randomize();
  }

}

// Random load/store sequence
// A random mix of load/store instructions and other instructions
class riscv_load_store_rand_instr_stream : riscv_load_store_base_instr_stream
{

  constraint!  q{
    num_load_store inside [10:30];
    num_mixed_instr inside [10:30];
  } legal_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }
}

// Use a small set of GPR to create various WAW, RAW, WAR hazard scenario
class riscv_hazard_instr_stream : riscv_load_store_base_instr_stream
{

  uint  num_of_avail_regs = 6;

  constraint! q{
    num_load_store inside [10:30];
    num_mixed_instr inside [10:30];
  } legal_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  override void pre_randomize() {
    avail_regs.length  = num_of_avail_regs;
    super.pre_randomize();
  }

}

// Use a small set of address to create various load/store hazard sequence
// This instruction stream focus more on hazard handling of load store unit.
class riscv_load_store_hazard_instr_stream : riscv_load_store_base_instr_stream
{

  @rand int hazard_ratio;

  constraint! q{
    hazard_ratio inside [20:100];
  }  hazard_ratio_c;

  constraint! q{
    num_load_store inside [10:20];
    num_mixed_instr inside [1:7];
  } legal_c;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  override void randomize_offset() {
    import std.algorithm: min, max;
    int offset_, addr_;
    offset.length  = num_load_store;
    addr.length = num_load_store;
    if (base < 0 || base > max_load_store_offset)
      assert (false);
    for (int i=0; i!=num_load_store; ++i) {
      if ((i > 0) && (urandom(0, 100) < hazard_ratio)) {
	offset[i] = offset[i-1];
	addr[i] = addr[i-1];
      }
      else {
	if (locality == locality_e.NARROW) {
	  offset_ = urandom!q{[]}(max(-16, 0-base), min(16, max_load_store_offset - 1 - base));
	}
	else if (locality == locality_e.HIGH) {
	  offset_ = urandom!q{[]}(max(-64, 0-base), min(64, max_load_store_offset - 1 - base));
	}
	else if (locality == locality_e.MEDIUM) {
	  offset_ = urandom!q{[]}(max(-256, 0-base), min(256, max_load_store_offset - 1 - base));
	}
	else if (locality == locality_e.SPARSE) {
	  offset_ = urandom!q{[]}(max(-2048, 0-base), min(2047, max_load_store_offset - 1 - base));
	}
	addr_ = base + offset_;
	if (addr_ < 0 || addr_ >= max_load_store_offset) assert (false);
	offset[i] = offset_;
	addr[i] = addr_;
      }
    }
  }

}

// Back to back access to multiple data pages
// This is useful to test data TLB switch and replacement
class riscv_multi_page_load_store_instr_stream: riscv_mem_access_stream
{
  mixin uvm_object_utils;

  riscv_load_store_stress_instr_stream[] load_store_instr_stream;
  @rand uint  num_of_instr_stream;
  @rand uint[]  data_page_id;
  @rand riscv_reg_t[] rs1_reg;

  constraint! q{
    foreach (id; data_page_id) {
      id < max_data_page_id;
    }
    data_page_id.length == num_of_instr_stream;
    rs1_reg.length == num_of_instr_stream;
    unique [rs1_reg];
    foreach(id; rs1_reg) {
      id !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
    }
  } default_c;

  constraint! q{
    // solve num_of_instr_stream before data_page_id;
    num_of_instr_stream inside [1 : max_data_page_id];
    unique [data_page_id];
  } page_c;

  // Avoid accessing a large number of pages because we may run out of registers for rs1
  // Each page access needs a reserved register as the base address of load/store instruction
  constraint! q{
    num_of_instr_stream inside [2:8];
  } reasonable_c;

  this(string name = "") {
    super(name);
  }

  // Generate each load/store seq, and mix them together
  override void post_randomize() {
    load_store_instr_stream.length  = num_of_instr_stream;
    foreach(i, ref instr; load_store_instr_stream) {
      instr = riscv_load_store_stress_instr_stream.type_id.
	create(format("load_store_instr_stream_%0d", i));
      instr.min_instr_cnt = 5;
      instr.max_instr_cnt = 10;
      instr.cfg = cfg;
      instr.hart = hart;
      instr.sp_c.constraint_mode(false);
      // Make sure each load/store sequence doesn't override the rs1 of other sequences.
      foreach(j , ref l; rs1_reg) {
	if(i != j) {
          instr.reserved_rd =
            (instr.reserved_rd ~ l);
        }
      }
      instr.randomize_with! q{
	rs1_reg == $0;
	data_page_id == $1;
      } (rs1_reg[i], data_page_id[i]);
      if (i == 0) {
        instr_list = instr.instr_list;
      }
      else {
        mix_instr_stream(instr.instr_list);
      }
    }
  }

}

// Access the different locations of the same memory regions
class riscv_mem_region_stress_test: riscv_multi_page_load_store_instr_stream
{
  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  constraint! q{
    num_of_instr_stream inside [2..5];
    foreach (i, id; data_page_id) {
      if (i > 0) {
        data_page_id[i] == data_page_id[i-1];
      }
    }
  } page_c;

}

// Random load/store sequence to full address range
// The address range is not preloaded with data pages, use store instruction to initialize first
class riscv_load_store_rand_addr_instr_stream : riscv_load_store_base_instr_stream
{
  @rand ubvec!XLEN  addr_offset;

  // Find an unused 4K page from address 1M onward
  constraint! q{
    addr_offset[XLEN-1:20] != 0;
    // TODO(taliu) Support larger address range
    addr_offset[XLEN-1:31] == 0;
    addr_offset[11:0] == 0;
  } addr_offset_c;

  constraint!  q{
    num_load_store inside [5:10];
    num_mixed_instr inside [5:10];
  } legal_c;


  mixin uvm_object_utils;
  this(string name = "") {
    super(name);
  }

  override  void randomize_offset() {
    // import std.conv: to;
    offset.length = num_load_store;
    addr.length = num_load_store;
    for (int i=0; i<num_load_store; i++) {
      offset[i] = urandom(-2048, 2048);
      addr[i] = cast(int) addr_offset + offset[i];
    }
  }

  override void add_rs1_init_la_instr(riscv_reg_t gpr, int id, int base = 0) {
    Queue!riscv_instr instr;
    riscv_pseudo_instr li_instr;
    riscv_instr store_instr;
    riscv_instr add_instr;
    int[] min_offset;
    int[] max_offset;
    min_offset ~=  offset.minElement;
    max_offset ~= offset.maxElement;
    // Use LI to initialize the address offset
    li_instr = riscv_pseudo_instr.type_id.create("li_instr");
    //DV_CHECK_RANDOMIZE_WITH_FATAL(li_instr,
    li_instr.randomize_with! q{
      pseudo_instr_name == riscv_pseudo_instr_name_t.LI;
      rd inside [$0];
      rd != $1;
    } (cfg.gpr, gpr);
    li_instr.imm_str = format("0x%0x", addr_offset);
    // Add offset to the base address
    add_instr = cfg.instr_registry.get_instr(riscv_instr_name_t.ADD);
    //`DV_CHECK_RANDOMIZE_WITH_FATAL(add_instr,

    add_instr.randomize_with! q{
      rs1 == $0;
      rs2 == $1;
      rd  == $0;
    }(gpr, li_instr.rd);
    instr ~= li_instr;
    instr ~= add_instr;
    // Create SW instruction template
    store_instr = cfg.instr_registry.get_instr(riscv_instr_name_t.SB);
    //`DV_CHECK_RANDOMIZE_WITH_FATAL(store_instr,
    store_instr.randomize_with! q{
      instr_name == riscv_instr_name_t.SB;
      rs1 == $0;
    }(gpr);
    // Initialize the location which used by load instruction later
    foreach (i, lsinstr; load_store_instr) {
      if (lsinstr.category == riscv_instr_category_t.LOAD) {
        riscv_instr store;
        store = riscv_instr.type_id.create("store");
        store.copy(store_instr);
        store.rs2 = cast(riscv_reg_t) ((cast(int) i) % 32);
        store.imm_str = lsinstr.imm_str;
        // TODO: C_FLDSP is in both rv32 and rv64 ISA
	switch (lsinstr.instr_name) {
	case riscv_instr_name_t.LB,
	  riscv_instr_name_t.LBU:
	  store.instr_name = riscv_instr_name_t.SB;
	  break;
	case riscv_instr_name_t.LH,
	  riscv_instr_name_t.LHU  :
	  store.instr_name = riscv_instr_name_t.SH;
	  break;
	case riscv_instr_name_t.LW,
	  riscv_instr_name_t.C_LW,
	  riscv_instr_name_t.C_LWSP,
	  riscv_instr_name_t.FLW,
	  riscv_instr_name_t.C_FLW,
	  riscv_instr_name_t.C_FLWSP:
	  store.instr_name = riscv_instr_name_t.SW;
	  break;
	case  riscv_instr_name_t.LD,
	  riscv_instr_name_t.C_LD,
	  riscv_instr_name_t.C_LDSP,
	  riscv_instr_name_t.FLD,
	  riscv_instr_name_t.C_FLD,
	  riscv_instr_name_t.LWU:
	  store.instr_name = riscv_instr_name_t.SD;
	    break;
	default: uvm_fatal(get_full_name(), format("Unexpected op: %0s",
						   lsinstr.convert2asm()));
	    break;
	}
	instr ~= store;
      }
    }
    prepend_instr_list(instr);
    super.add_rs1_init_la_instr(gpr, id, 0);
  }

}


class riscv_vector_load_store_instr_stream : riscv_mem_access_stream
{
  enum address_mode_e {UNIT_STRIDED, STRIDED, INDEXED}

  @rand ubvec!11 eew;
  @rand uint  data_page_id;
  @rand uint  num_mixed_instr;
  @rand uint  stride_byte_offset;
  @rand uint  index_addr;
  @rand address_mode_e address_mode;
  @rand riscv_reg_t rs1_reg;  // Base address
  @rand riscv_reg_t rs2_reg;  // Stride offset
  riscv_vreg_t vs2_reg;      // Index address

  constraint!  q{
    num_mixed_instr inside [0:10];
  } vec_mixed_instr_c;

  constraint!  q{
    solve eew before stride_byte_offset;
    // Keep a reasonable byte offset range to avoid vector memory address overflow
    stride_byte_offset inside [1 : 128];
    stride_byte_offset % (eew / 8) == 1;
  } stride_byte_offset_c;

  constraint! q{
    solve eew before index_addr;
    // Keep a reasonable index address range to avoid vector memory address overflow
    index_addr inside [1 : 128];
    index_addr % (eew / 8) == 1;
  } index_addr_c;

  constraint!  q{
    rs1_reg !inside [cfg.reserved_regs, reserved_rd, riscv_reg_t.ZERO];
    rs2_reg !inside [cfg.reserved_regs, reserved_rd, riscv_reg_t.ZERO];
    rs1_reg != rs2_reg;
  } vec_rs_c;

  constraint!  q{
    data_page_id < max_data_page_id;
  } vec_data_page_id_c;

  int base;
  int max_load_store_addr;
  riscv_vector_instr load_store_instr;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  override void post_randomize() {
    reserved_rd ~= rs1_reg;
    reserved_rd ~= rs2_reg;
    randomize_avail_regs();
    gen_load_store_instr();
    randomize_addr();
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);
    if (address_mode == address_mode_e.STRIDED) {
      this.append_instr(get_init_gpr_instr(rs2_reg, toubvec!XLEN(stride_byte_offset)));
    }
    else if (address_mode == address_mode_e.INDEXED) {
      // TODO: Support different index address for each element
      add_init_vector_gpr_instr(vs2_reg, toubvec!XLEN(index_addr));
    }
    super.post_randomize();
  }

  void randomize_addr() {
    int ss = address_span();
    bool success;

    for (int i=0; i<10; ++i) {
      max_load_store_addr = data_page[data_page_id].size_in_bytes - ss;
      if (max_load_store_addr >= 0) {
	success = true;
        break;
      }
      //DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_page_id, data_page_id < max_data_page_id;)
      assert (max_data_page_id != 0);
      data_page_id = urandom(0, max_data_page_id);
    }

    if (success != true) {
      uvm_fatal(get_full_name(), format(("Expected positive value for max_load_store_addr, got %0d." ~
					 "  Perhaps more memory needs to be allocated in the data pages for vector loads and stores." ~
					 "\ndata_page_id:%0d\ndata_page[data_page_id].size_in_bytes:%0d\naddress_span:%0d" ~
					 "\nstride_bytes:%0d\nVLEN:%0d\nLMUL:%0d\ncfg.vector_cfg.vtype.vsew:%0d\n\n"),
					max_load_store_addr, data_page_id, data_page[data_page_id].size_in_bytes, ss,
					stride_bytes(), VLEN,
					cfg.vector_cfg.vtype.vlmul, cfg.vector_cfg.vtype.vsew));
    }

    // `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(base, base >= 0; base <= max_load_store_addr;)

    base = urandom!q{[]}(0, max_load_store_addr);
    base = (cast(int) eew) * base/(cast(int) eew);
  }

  int address_span() {
    int num_elements = VLEN * cfg.vector_cfg.vtype.vlmul / cfg.vector_cfg.vtype.vsew;
    switch (address_mode) {
    case (address_mode_e.UNIT_STRIDED) : return  num_elements * stride_bytes();
    case (address_mode_e.STRIDED)      : return num_elements * stride_byte_offset;
    case (address_mode_e.INDEXED)      : return index_addr + num_elements * stride_bytes();
    default : return  0 ;
    }
  }

  int stride_bytes() {
    return cast(int) eew / 8;
  }

  // Generate each load/store instruction
  void gen_load_store_instr() {
    build_allowed_instr();
    randomize_vec_load_store_instr();
    this.append_instr(load_store_instr);
  }

  void build_allowed_instr() {
    switch (address_mode) {
    case address_mode_e.UNIT_STRIDED:
      allowed_instr = [riscv_instr_name_t.VLE_V, riscv_instr_name_t.VSE_V] ~ allowed_instr;
      if (cfg.vector_cfg.enable_fault_only_first_load) {
	allowed_instr = [riscv_instr_name_t.VLEFF_V] ~ allowed_instr;
      }
      if (cfg.vector_cfg.enable_zvlsseg) {
	allowed_instr = [riscv_instr_name_t.VLSEGE_V, riscv_instr_name_t.VSSEGE_V] ~ allowed_instr;
	if (cfg.vector_cfg.enable_fault_only_first_load) {
	  allowed_instr = [riscv_instr_name_t.VLSEGEFF_V] ~ allowed_instr;
	}
      }
      break;
    case address_mode_e.STRIDED:
      allowed_instr = [riscv_instr_name_t.VLSE_V, riscv_instr_name_t.VSSE_V] ~ allowed_instr;
      if (cfg.vector_cfg.enable_zvlsseg) {
	allowed_instr = [riscv_instr_name_t.VLSSEGE_V, riscv_instr_name_t.VSSSEGE_V] ~ allowed_instr;
      }
      break;
    case address_mode_e.INDEXED:
      allowed_instr = [riscv_instr_name_t.VLXEI_V, riscv_instr_name_t.VSXEI_V,
		       riscv_instr_name_t.VSUXEI_V] ~ allowed_instr;
      if (cfg.vector_cfg.enable_zvlsseg) {
	allowed_instr = [riscv_instr_name_t.VLXSEGEI_V, riscv_instr_name_t.VSXSEGEI_V,
			 riscv_instr_name_t.VSUXSEGEI_V] ~ allowed_instr;
      }
      break;
    default: break;
    }
  }

  void randomize_vec_load_store_instr() {
    load_store_instr =
      cast(riscv_vector_instr) cfg.instr_registry.get_load_store_instr(allowed_instr);
    load_store_instr.m_cfg = cfg;
    load_store_instr.has_rs1 = false;
    load_store_instr.has_vs2 = true;
    load_store_instr.has_imm = false;
    randomize_gpr(load_store_instr);
    load_store_instr.rs1 = rs1_reg;
    load_store_instr.rs2 = rs2_reg;
    load_store_instr.vs2 = vs2_reg;
    if (address_mode == address_mode_e.INDEXED) {
      cfg.vector_cfg.reserved_vregs = [load_store_instr.vs2];
      vs2_reg = load_store_instr.vs2;
      uvm_info(get_full_name(), format("vs2_reg = v%0d", vs2_reg), UVM_LOW);
    }
    load_store_instr.process_load_store = 0;
  }

}
