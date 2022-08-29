/*
 * Copyright 2020 Google LLC
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

module riscv.gen.riscv_vector_cfg;

import riscv.gen.riscv_instr_pkg: riscv_vreg_t, vxrm_t, vtype_t;
import riscv.gen.target: XLEN, VLEN, MAX_LMUL, ELEN, SELEN;

import std.string: format, toUpper, toLower, strip;

import esdl.data.bvec: ubvec;
import esdl.rand: constraint, rand;
import uvm;


class riscv_vector_cfg : uvm_object
{

  mixin uvm_object_utils;

  @rand @UVM_DEFAULT vtype_t       vtype;
  @rand @UVM_DEFAULT ubvec!XLEN    vl;
  @rand @UVM_DEFAULT ubvec!XLEN    vstart;
  @rand @UVM_DEFAULT vxrm_t        vxrm;
  @rand @UVM_DEFAULT bool          vxsat;

  riscv_vreg_t[]      reserved_vregs;

  // Allowed effective element width based on the LMUL setting
  @UVM_DEFAULT uint[]           legal_eew;

  // Allow only vector instructions from the random sequences
  @rand bool only_vec_instr;

  constraint! q{@soft only_vec_instr == false;} only_vec_instr_c;

  // Allow vector floating-point instructions (Allows vtype.vsew to be set <16 or >32).
  @rand bool vec_fp;

  // Allow vector narrowing or widening instructions.
  @rand bool vec_narrowing_widening;

  // Allow vector quad-widening instructions.
  @rand bool vec_quad_widening;

  constraint! q{
    (!vec_narrowing_widening) -> (!vec_quad_widening);
    // FP requires at least 16 bits and quad-widening requires no more than ELEN/4 bits.
    (ELEN < 64) -> (!(vec_fp && vec_quad_widening));
  } vec_quad_widening_c ;

  @rand bool allow_illegal_vec_instr;
  constraint! q{@soft allow_illegal_vec_instr == false;} allow_illegal_vec_instr_c;

  // Cause frequent hazards for the Vector Registers:
  //  * Write-After-Read (WAR)
  //  * Read-After-Write (RAW)
  //  * Read-After-Read (RAR)
  //  * Write-After-Write (WAW)
  // These hazard conditions are induced by keeping a small (~5) list of registers to select from.
  @rand bool vec_reg_hazards;

  // Enable segmented load/store extension ops
  @rand @UVM_DEFAULT bool enable_zvlsseg = true;

  // Enable fault only first load ops
  @rand @UVM_DEFAULT bool enable_fault_only_first_load;


   constraint! q{
     //solve vtype before vl;
     //solve vl before vstart;
     vstart inside [0:vl];
     vl inside [1:VLEN/vtype.vsew];
   } legal_c;

  // Basic constraint for initial bringup
   constraint! q{
     vstart == 0;
     vl == VLEN/vtype.vsew;
     vtype.vediv == 1;
   } bringup_c;

  // For all widening instructions, the destination element width must be a supported element
  // width and the destination LMUL value must also be a supported LMUL value
   constraint! q{
     vtype.vlmul inside [1, 2, 4, 8];
     vtype.vlmul <= MAX_LMUL;
     if (vec_narrowing_widening) {
       (vtype.vlmul < 8) || (vtype.fractional_lmul == true);
     }
     if (vec_quad_widening) {
       vtype.vlmul < 4 || (vtype.fractional_lmul == true);
     }
   } vlmul_c ;

   constraint! q{
     vtype.vsew inside [8, 16, 32, 64, 128];
     vtype.vsew <= ELEN;
     // TODO: Determine the legal range of floating point format
     if (vec_fp) {vtype.vsew inside [32];}
     if (vec_narrowing_widening) {vtype.vsew < ELEN;}
     if (vec_quad_widening) {vtype.vsew < (ELEN >> 1);}
   } vsew_c;

   constraint! q{
     enable_zvlsseg -> (vtype.vlmul < 8);
   } vseg_c;

   constraint!  q{
     vtype.vediv inside [1, 2, 4, 8];
     vtype.vediv <= (vtype.vsew / SELEN);
   } vdeiv_c;


  this(string name = "") {
    import esdl.base.cmdl: CommandLine;
    super(name);
    CommandLine cmdl = new CommandLine();
    //if ($value$plusargs("enable_zvlsseg=%0d", enable_zvlsseg)) begin
    if (cmdl.plusArgs("enable_zvlsseg=%d", enable_zvlsseg)) {
      rand_mode!"enable_zvlsseg"(false);
    }
    if (cmdl.plusArgs("enable_fault_only_first_load=%d", enable_fault_only_first_load)) {
      rand_mode!"enable_fault_only_first_load"(false);
    }
  }

  void post_randomize() {
    real temp_eew;
    legal_eew.length = 0;
    // Section 7.3 Vector loads and stores have the EEW encoded directly in the instruction.
    // EMUL is calculated as EMUL =(EEW/SEW)*LMUL. If the EMUL would be out of range
    // (EMUL>8 or EMUL<1/8), an illegal instruction exceptionis raised.
    // EEW = SEW * EMUL / LMUL
    for (real emul = 0.125; emul <= 8; emul = emul * 2) {
      if (vtype.fractional_lmul == 0) {
	temp_eew = cast(real) (vtype.vsew) * emul/cast(real) (vtype.vlmul);
      }
      else {
	temp_eew = cast(real) (vtype.vsew) * emul * cast(real) (vtype.vlmul);
      }
      if (temp_eew >= 8 && temp_eew <= 1024) {
	legal_eew ~= cast(uint) (temp_eew);
      }
      uvm_info(get_full_name(), format("Checking emul: %.2f", emul), UVM_LOW);
    }
  }

}
