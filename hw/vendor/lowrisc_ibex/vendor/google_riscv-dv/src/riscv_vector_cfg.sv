/*
 * Copyright 2020 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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

class riscv_vector_cfg extends uvm_object;

  rand vtype_t           vtype;
  rand bit [XLEN-1:0]    vl;
  rand bit [XLEN-1:0]    vstart;
  rand vxrm_t            vxrm;
  rand bit               vxsat;
  riscv_vreg_t           reserved_vregs[$];

  // Allowed effective element width based on the LMUL setting
  int unsigned           legal_eew[$];

  // Allow only vector instructions from the random sequences
  rand bit only_vec_instr;
  constraint only_vec_instr_c {soft only_vec_instr == 0;}

  // Allow vector floating-point instructions (Allows vtype.vsew to be set <16 or >32).
  rand bit vec_fp;

  // Allow vector narrowing or widening instructions.
  rand bit vec_narrowing_widening;

  // Allow vector quad-widening instructions.
  rand bit vec_quad_widening;

  constraint vec_quad_widening_c {
    (!vec_narrowing_widening) -> (!vec_quad_widening);
    // FP requires at least 16 bits and quad-widening requires no more than ELEN/4 bits.
    (ELEN < 64) -> (!(vec_fp && vec_quad_widening));
  }

  rand bit allow_illegal_vec_instr;
  constraint allow_illegal_vec_instr_c {soft allow_illegal_vec_instr == 0;}

  // Cause frequent hazards for the Vector Registers:
  //  * Write-After-Read (WAR)
  //  * Read-After-Write (RAW)
  //  * Read-After-Read (RAR)
  //  * Write-After-Write (WAW)
  // These hazard conditions are induced by keeping a small (~5) list of registers to select from.
  rand bit vec_reg_hazards;

  // Enable segmented load/store extension ops
  rand bit enable_zvlsseg = 1'b1;

  // Enable fault only first load ops
  rand bit enable_fault_only_first_load;

  constraint legal_c {
    solve vtype before vl;
    solve vl before vstart;
    vstart inside {[0:vl]};
    vl inside {[1:VLEN/vtype.vsew]};
  }

  // Basic constraint for initial bringup
  constraint bringup_c {
    vstart == 0;
    vl == VLEN/vtype.vsew;
    vtype.vediv == 1;
  }

  // For all widening instructions, the destination element width must be a supported element
  // width and the destination LMUL value must also be a supported LMUL value
  constraint vlmul_c {
    vtype.vlmul inside {1, 2, 4, 8};
    vtype.vlmul <= MAX_LMUL;
    if (vec_narrowing_widening) {
      (vtype.vlmul < 8) || (vtype.fractional_lmul == 1'b1);
    }
    if (vec_quad_widening) {
      (vtype.vlmul < 4) || (vtype.fractional_lmul == 1'b1);
    }
  }

  constraint vsew_c {
    vtype.vsew inside {8, 16, 32, 64, 128};
    vtype.vsew <= ELEN;
    // TODO: Determine the legal range of floating point format
    if (vec_fp) {vtype.vsew inside {32};}
    if (vec_narrowing_widening) {vtype.vsew < ELEN;}
    if (vec_quad_widening) {vtype.vsew < (ELEN >> 1);}
  }

  constraint vseg_c {
    enable_zvlsseg -> (vtype.vlmul < 8);
  }

  constraint vdeiv_c {
    vtype.vediv inside {1, 2, 4, 8};
    vtype.vediv <= (vtype.vsew / SELEN);
  }

  `uvm_object_utils_begin(riscv_vector_cfg)
    `uvm_field_int(vtype.ill, UVM_DEFAULT)
    `uvm_field_int(vtype.vediv, UVM_DEFAULT)
    `uvm_field_int(vtype.vsew, UVM_DEFAULT)
    `uvm_field_int(vtype.vlmul, UVM_DEFAULT)
    `uvm_field_int(vtype.fractional_lmul, UVM_DEFAULT)
    `uvm_field_queue_int(legal_eew, UVM_DEFAULT)
    `uvm_field_int(vl, UVM_DEFAULT)
    `uvm_field_int(vstart, UVM_DEFAULT)
    `uvm_field_enum(vxrm_t,vxrm, UVM_DEFAULT)
    `uvm_field_int(vxsat, UVM_DEFAULT)
    `uvm_field_int(enable_zvlsseg, UVM_DEFAULT)
    `uvm_field_int(enable_fault_only_first_load, UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
    if ($value$plusargs("enable_zvlsseg=%0d", enable_zvlsseg)) begin
      enable_zvlsseg.rand_mode(0);
    end
    if ($value$plusargs("enable_fault_only_first_load=%0d", enable_fault_only_first_load)) begin
      enable_fault_only_first_load.rand_mode(0);
    end
  endfunction : new

  function void post_randomize();
    real temp_eew;
    legal_eew = {};
    // Section 7.3 Vector loads and stores have the EEW encoded directly in the instruction.
    // EMUL is calculated as EMUL =(EEW/SEW)*LMUL. If the EMUL would be out of range
    // (EMUL>8 or EMUL<1/8), an illegal instruction exceptionis raised.
    // EEW = SEW * EMUL / LMUL
    for (real emul = 0.125; emul <= 8; emul = emul * 2) begin
      if (vtype.fractional_lmul == 0) begin
        temp_eew = real'(vtype.vsew) * emul / real'(vtype.vlmul);
      end else begin
        temp_eew = real'(vtype.vsew) * emul * real'(vtype.vlmul);
      end
      if (temp_eew inside {[8:1024]}) begin
        legal_eew.push_back(int'(temp_eew));
      end
      `uvm_info(`gfn, $sformatf("Checking emul: %.2f", emul), UVM_LOW)
    end
  endfunction : post_randomize

endclass : riscv_vector_cfg
