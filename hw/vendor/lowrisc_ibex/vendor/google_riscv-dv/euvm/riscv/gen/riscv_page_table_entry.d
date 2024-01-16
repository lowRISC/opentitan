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

//--------------------------------------------------------------------------------------------
// RISC-V Page Table Entry(PTE)
//
// Support SV32, SV39, SV48 PTE format defined in RISC-V privileged spec 1.10.
// -------------------------------------------------------------------------------------------
module riscv.gen.riscv_page_table_entry;


import riscv.gen.riscv_instr_pkg: pte_permission_t, satp_mode_t;
import riscv.gen.target: XLEN;
import std.format: format;

import esdl.data.bvec: ubvec;
import esdl.rand: constraint, rand;

import uvm;

version(CHECK_COMPILE) alias riscv_page_table_entry_SV39 = riscv_page_table_entry!(satp_mode_t.SV39);

class riscv_page_table_entry(satp_mode_t MODE = satp_mode_t.SV39) : uvm_object
{

  enum int PPN0_WIDTH  = (MODE == satp_mode_t.SV32) ? 10 : 9;
  enum int PPN1_WIDTH  = (MODE == satp_mode_t.SV32) ? 12 : 9;
  enum int PPN2_WIDTH  = (MODE == satp_mode_t.SV39) ? 26 : ((MODE == satp_mode_t.SV48) ? 9 : 1);
  enum int PPN3_WIDTH  = (MODE == satp_mode_t.SV48) ? 9  : 1;
  enum int RSVD_WIDTH  = (MODE == satp_mode_t.SV32) ? 1  : 10;
  enum int VPN_WIDTH   = (MODE == satp_mode_t.SV32) ? 10 : 9;
  // Spare bits in virtual address = XLEN - used virtual address bits
  enum int VADDR_SPARE = (MODE == satp_mode_t.SV32) ? 0  : (MODE == satp_mode_t.SV39) ? 25 : 16;
  // Virtual address bit width
  enum int VADDR_WIDTH = (MODE == satp_mode_t.SV32) ? 31 : (MODE == satp_mode_t.SV39) ? 38 : 48;

  mixin uvm_object_utils;
  //`uvm_object_param_utils(riscv_page_table_entry#(MODE))
  //`uvm_object_new

  this(string name = "") {
    super(name);
  }

  @rand bool                    v;     // PTE is valid
  @rand pte_permission_t        xwr;   // PTE execute-write-read permission
  @rand bool                    u;     // Accessible in User Mode
  @rand bool                    g;     // Gloabal mapping
  @rand bool                    a;     // Accessed flag
  @rand bool                    d;     // Dirty flag
  @rand ubvec!2                 rsw;   // Reserved for future use
  @rand ubvec!PPN0_WIDTH        ppn0;
  @rand ubvec!PPN1_WIDTH        ppn1;
  @rand ubvec!PPN2_WIDTH        ppn2;
  @rand ubvec!PPN3_WIDTH        ppn3;
  @rand ubvec!XLEN              bits;
  @rand ubvec!RSVD_WIDTH        rsvd;
  int                           child_table_id;
  ubvec!XLEN                    starting_pa; // Starting physical address
  ubvec!XLEN                    starting_va; // Starting virtual address offset

  // This two bits are implementation specific, set them to 1 to avoid mismatching
  constraint! q{
    @soft a    == true;
    @soft d    == true;
  } access_dirty_bit_c;

  // Set reserved fields to 0
  constraint! q{
    @soft rsw  == 0;
    @soft rsvd == 0;
  } reserved_bits_c;

  // PPN is assigned in the post-process
  constraint! q{
    @soft ppn0 == 0;
    @soft ppn1 == 0;
    @soft ppn2 == 0;
    @soft ppn3 == 0;
  } ppn_zero_c;

  constraint! q{
    // If the PTE is not a leaf page, U,A,D must be cleared by SW for future compatibility
    if (xwr == pte_permission_t.NEXT_LEVEL_PAGE) {
      u == false;
      a == false;
      d == false;
    }
  } sw_legal_c;


  void turn_off_default_constraint() {
    access_dirty_bit_c.constraint_mode(false);
    reserved_bits_c.constraint_mode(false);
    ppn_zero_c.constraint_mode(false);
    sw_legal_c.constraint_mode(false);
  }

  void post_randomize() {
    pack_entry();
  }

  override void do_copy(uvm_object rhs) {
    super.do_copy(rhs);
    riscv_page_table_entry!(MODE) rhs_ =
      cast(riscv_page_table_entry!MODE) rhs;
    //`DV_CHECK_FATAL($cast(rhs_, rhs), "Cast to page_table_entry failed!")
    this.v = rhs_.v;
    this.xwr = rhs_.xwr;
    this.u = rhs_.u;
    this.g = rhs_.g;
    this.a = rhs_.a;
    this.d = rhs_.d;
    this.rsw = rhs_.rsw;
    this.ppn0 = rhs_.ppn0;
    this.ppn1 = rhs_.ppn1;
    this.ppn2 = rhs_.ppn2;
    this.ppn3 = rhs_.ppn3;
    this.bits = rhs_.bits;
    this.rsvd = rhs_.rsvd;
    this.starting_pa = rhs_.starting_pa;
    this.starting_va = rhs_.starting_va;
    this.child_table_id = rhs_.child_table_id;
  }

  override string convert2string() {
    string str = format("xwr: %0s, (v)alid:%0d, u: %0d, pa:0x%0x, va:0x%0x",
			xwr, v, u, starting_pa, starting_va);
    switch (MODE) {
    case satp_mode_t.SV32:
      str = str ~ format(", ppn[1:0] = %0d/%0d", ppn1, ppn0);
      break;
    case satp_mode_t.SV39:
      str = str ~ format(", ppn[2:0] = %0d/%0d/%0d", ppn2, ppn1, ppn0);
      break;
    case satp_mode_t.SV48 :
      str =  str ~  format(", ppn[3:0] = %0d/%0d/%0d/%0d", ppn3, ppn2, ppn1, ppn0);
      break;
    default:
      uvm_fatal(get_full_name(), format("Unsupported mode %0x", MODE));
      break;
    }
    return str;
  }

  // Pack the PTE to bit stream
  void pack_entry() {
    switch (MODE) {
    case satp_mode_t.SV32:
      bits = cast(ubvec!XLEN) (ppn1 ~ ppn0 ~ rsw ~ d ~ a ~ g ~ u ~ xwr ~ v);
      break;
    case satp_mode_t.SV39:
      bits = cast(ubvec!XLEN) (rsvd ~ ppn2 ~ ppn1 ~ ppn0 ~ rsw ~ d ~ a ~ g ~ u ~ xwr ~ v);
      break;
    case satp_mode_t.SV48:
      bits = cast(ubvec!XLEN) (rsvd ~ ppn3 ~ ppn2 ~ ppn1 ~ ppn0 ~ rsw ~ d ~ a ~ g ~ u ~ xwr ~ v);
      break;
    default:
      uvm_fatal(get_full_name(), format("Unsupported mode %0x", MODE));
      break;
    }
  }


  // Return the PPN field offset based on the page level
   int get_ppn_offset(ubvec!2 page_level) {
     switch (page_level) {
     case 0:
       return 0;
     case 1:
       return PPN0_WIDTH;
     case 2:
       return PPN0_WIDTH + PPN1_WIDTH;
     case 3:
       return PPN0_WIDTH + PPN1_WIDTH + PPN2_WIDTH;
     default:  uvm_fatal(get_full_name(),
			 format("Unsupported page_level %0x", page_level));
       assert (false);
    }
  }

  // Assign each PPN field based on the input physical address. This function //is used to setup the
  // leaf PTE to map to the target physical address.
  // start_pa   : Start phyical address.
  // pte_index  : The PTE index of the input page level.
  // page_level : The page level that this PTE belongs to.

  void set_ppn(ubvec!XLEN base_pa, int pte_index, ubvec!2 page_level) {
    int[4] pte_incr;
    int pte_per_table = 4096 / (XLEN/8);
    ppn0 = cast(ubvec!PPN0_WIDTH) (base_pa[12 .. 12 + PPN0_WIDTH]);
    ppn1 = cast(ubvec!PPN1_WIDTH) (base_pa[12 +  PPN0_WIDTH ..12 +  PPN0_WIDTH + PPN1_WIDTH]);
    if (MODE == satp_mode_t.SV39) {
      ppn2 = cast(ubvec!PPN2_WIDTH) (base_pa[12 + PPN0_WIDTH + PPN1_WIDTH ..12 + PPN0_WIDTH + PPN1_WIDTH+ PPN2_WIDTH]);
    }
    else if (MODE == satp_mode_t.SV48) {
      ppn2 = cast(ubvec!PPN2_WIDTH) (base_pa[12 + PPN0_WIDTH + PPN1_WIDTH .. 12 + PPN0_WIDTH + PPN1_WIDTH + PPN2_WIDTH]);
      ppn3 = cast(ubvec!PPN3_WIDTH) (base_pa[12 + PPN0_WIDTH + PPN1_WIDTH +  PPN2_WIDTH ..12 + PPN0_WIDTH + PPN1_WIDTH +  PPN2_WIDTH+ PPN3_WIDTH]);
    }
    foreach (i; pte_incr) {
      if (i >= page_level) {
	pte_incr[i] = pte_index % pte_per_table;
	pte_index = pte_index / pte_per_table;
      }
    }
    ppn0 += pte_incr[0];
    ppn1 += pte_incr[1];
    ppn2 += pte_incr[2];
    ppn3 += pte_incr[3];
    starting_pa = get_starting_pa();
    starting_va = starting_pa - base_pa;
  }

  // Get the starting physical address covered by this PTE
  ubvec!XLEN get_starting_pa() {
    ubvec!XLEN retval;
    switch(MODE) {
    case satp_mode_t.SV32:
      retval = ppn1 ~ ppn0;
      break;
    case satp_mode_t.SV39:
      retval = ppn2 ~ ppn1 ~ ppn0;
      break;
    case satp_mode_t.SV48:
      retval = ppn3 ~ ppn2 ~ ppn1 ~ ppn0;
      break;
    default:
      uvm_fatal(get_full_name(),
		format("Unsupported mode %0x", MODE));
      break;
    }
    retval <<= 12;
    return retval;
  }
}


