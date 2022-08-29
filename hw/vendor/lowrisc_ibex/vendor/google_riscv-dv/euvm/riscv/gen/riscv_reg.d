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

// --------------------------------------------------
// Light weight RISC-V register class library
// --------------------------------------------------

// Base class for RISC-V register field

module riscv.gen.riscv_reg;


import esdl.data.bvec: ubvec, toubvec;
import riscv.gen.riscv_instr_pkg: reg_field_access_t, privileged_reg_t,
  privileged_level_t, riscv_csr_t;
import riscv.gen.target: XLEN;
import std.format: format;

import esdl.rand: rand, constraint, randomize;
import uvm;

class riscv_reg_field: uvm_object
{
  mixin uvm_object_utils;

  uint                    bit_width;
  ubvec!XLEN              reset_val ;
  @rand ubvec!XLEN        val;
  reg_field_access_t      access_type;
  bool                    hard_wired;

  constraint! q{
    (access_type == reg_field_access_t.WPRI) -> (val == 0);
  } zero_reserved_field_c;

  constraint! q{
    (hard_wired == true) -> (val == reset_val);
  } hardwired_fld_c;


  this(string name = "") {
    super(name);
  }

  override string convert2string() {
    return(format("%0s bit_width:%0d val:0x%0x type:%0s",
		  get_name(), bit_width, val, access_type));
  }


  void post_randomize() {
    ubvec!XLEN mask = ubvec!XLEN.max();
    mask >>= (XLEN-bit_width);
    val = mask & val;
  }
}

version(CHECK_COMPILE) alias riscv_reg_privileged_reg_t = riscv_reg!(privileged_reg_t);

// Base class for RISC-V register
class riscv_reg(REG_T): uvm_object
{
  mixin uvm_object_utils;

  REG_T                         reg_name;
  riscv_csr_t                   offset;
  privileged_level_t            privil_level;
  ubvec!XLEN                    val;
  @rand riscv_reg_field[]       fld;

  this(string name = "") {
    super(name);
  }

  void init_reg(REG_T reg_name) {
    this.reg_name = reg_name;
    offset = toubvec!12(reg_name);
  }

  ubvec!XLEN get_val() {
    import std.stdio: writeln;

    int total_len = 0;
    // total_len = fld.sum() with (item.bit_width);
    foreach (f; fld) total_len = total_len + f.bit_width;

    if (total_len != XLEN) {
      foreach (f; fld) {
	writeln(format(f.convert2string()));
	uvm_fatal(get_full_name(),
		  format("Total field length %0d != XLEN %0d", total_len, XLEN));
      }
    }
    val = 0;
    foreach (f; fld) {
      val = (val << f.bit_width) | f.val;
    }
    return val;
  }

  void add_field(string fld_name, uint  bit_width,
		 reg_field_access_t access_type,
		 ubvec!XLEN reset_val = 0) {
    riscv_reg_field new_fld;
    new_fld = riscv_reg_field.type_id.create(fld_name);
    new_fld.bit_width = bit_width;
    new_fld.access_type = access_type;
    new_fld.reset_val = reset_val;
    fld ~= new_fld;
  }

  void set_field(T)(string fld_name, T val, bool hard_wired = false) {
    ubvec!XLEN val_ = val;
    set_field_bvec(fld_name, val_, hard_wired);
  }

  void set_field_bvec(string fld_name, ubvec!XLEN val, bool hard_wired = false) {
    foreach (f; fld) {
      if (fld_name == (f.get_name())) {
        f.val = val;
        f.hard_wired = hard_wired;
        if (hard_wired) {
	  f.reset_val = val;
	}
        return;
      }
    }
    uvm_fatal(get_full_name(), format("Cannot match found field %0s", fld_name));
  }

  riscv_reg_field get_field_by_name(string fld_name) {
    foreach (f; fld) {
      if (fld_name == (f.get_name())) {
        return f;
      }
    }
    uvm_fatal(get_full_name(), format("Cannot match found field %0s", fld_name));
    return null;
  }

  void rand_field(string fld_name) {
    riscv_reg_field fld_hd = get_field_by_name(fld_name);
    // `DV_CHECK_RANDOMIZE_FATAL(fld_hd)
    fld_hd.randomize();
  }

  void set_field_rand_mode(string fld_name, bool rand_on) {
    riscv_reg_field fld_hd = get_field_by_name(fld_name);
    // rand_mode!q{fld_hd}(rand_on); // TBD
  }

  void reset() {
    foreach (f; fld) {
      f.val = f.reset_val;
    }
  }

  void set_val(ubvec!XLEN val) {
    foreach (f; fld) {
      if (! f.hard_wired) {
        // Assign the valid msb to the field
        f.val = (val >> (XLEN - f.bit_width));
        uvm_info(get_full_name(),
		 format("Assign field %0s, bit_width:%0d, reg_val 0x%0x,  fld_val:0x%0x",
			f.get_name(), f.bit_width, val, f.val), UVM_LOW);
      }
      val <<= f.bit_width;
    }
  }

}
