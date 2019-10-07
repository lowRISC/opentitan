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

// --------------------------------------------------
// Light weight RISC-V register class library
// --------------------------------------------------

// Base class for RISC-V register field
class riscv_reg_field extends uvm_object;

  int unsigned                bit_width;
  bit [XLEN-1:0]              reset_val;
  rand bit [XLEN-1:0]         val;
  reg_field_access_t          access_type;
  bit                         hard_wired;

  constraint zero_reserved_field_c {
    (access_type == WPRI) -> (val == '0);
  }

  constraint hardwired_fld_c {
    (hard_wired) -> (val == reset_val);
  }

  `uvm_object_utils(riscv_reg_field)

  function new(string name = "");
    super.new(name);
  endfunction

  function string convert2string();
    return($sformatf("%0s bit_width:%0d val:0x%0x type:%0s",
                     get_name(), bit_width, val, access_type));
  endfunction

  function void post_randomize();
    bit [XLEN-1:0] mask = '1;
    mask = mask >> (XLEN-bit_width);
    val = mask & val;
  endfunction

endclass

// Base class for RISC-V register
class riscv_reg#(type REG_T = privileged_reg_t) extends uvm_object;

  REG_T                         reg_name;
  riscv_csr_t                   offset;
  privileged_level_t            privil_level;
  bit [XLEN-1:0]                val;
  rand riscv_reg_field          fld[$];

  `uvm_object_param_utils(riscv_reg#(REG_T))

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void init_reg(REG_T reg_name);
    this.reg_name = reg_name;
    offset = riscv_csr_t'(reg_name);
  endfunction

  virtual function bit[XLEN-1:0] get_val();
    int total_len;
    total_len = fld.sum() with (item.bit_width);
    if(total_len != XLEN) begin
      foreach(fld[i])
        $display(fld[i].convert2string());
      `uvm_fatal(get_full_name(),
                 $sformatf("Total field length %0d != XLEN %0d", total_len, XLEN))
    end
    val = '0;
    foreach(fld[i]) begin
      val = (val << fld[i].bit_width) | fld[i].val;
    end
    return val;
  endfunction

  virtual function void add_field(string fld_name, int unsigned bit_width,
                                  reg_field_access_t access_type,
                                  bit [XLEN-1:0] reset_val = '0);
    riscv_reg_field new_fld;
    new_fld = riscv_reg_field::type_id::create(fld_name);
    new_fld.bit_width = bit_width;
    new_fld.access_type = access_type;
    new_fld.reset_val = reset_val;
    fld.push_front(new_fld);
  endfunction

  virtual function void set_field(string fld_name, bit[XLEN-1:0] val, bit hard_wired = 1'b0);
    foreach(fld[i]) begin
      if(fld_name == fld[i].get_name()) begin
        fld[i].val = val;
        fld[i].hard_wired = hard_wired;
        if(hard_wired) begin
          fld[i].reset_val = val;
        end
        return;
      end
    end
    `uvm_fatal(get_full_name(), $sformatf("Cannot match found field %0s", fld_name))
  endfunction

  virtual function riscv_reg_field get_field_by_name(string fld_name);
    foreach(fld[i]) begin
      if(fld_name == fld[i].get_name()) begin
        return fld[i];
      end
    end
    `uvm_fatal(get_full_name(), $sformatf("Cannot match found field %0s", fld_name))
  endfunction

  virtual function void rand_field(string fld_name);
    riscv_reg_field fld_hd = get_field_by_name(fld_name);
    `DV_CHECK_RANDOMIZE_FATAL(fld_hd)
  endfunction

  virtual function void set_field_rand_mode(string fld_name, bit rand_on);
    riscv_reg_field fld_hd = get_field_by_name(fld_name);
    fld_hd.rand_mode(rand_on);
  endfunction

  virtual function void reset();
    foreach(fld[i]) begin
      fld[i].val = fld[i].reset_val;
    end
  endfunction

  virtual function void set_val(bit [XLEN-1:0] val);
    foreach(fld[i]) begin
      if(!fld[i].hard_wired) begin
        // Assign the valid msb to the field
        fld[i].val = (val >> (XLEN - fld[i].bit_width));
        `uvm_info(get_full_name(), $sformatf(
                  "Assign field %0s, bit_width:%0d, reg_val 0x%0x,  fld_val:0x%0x",
                  fld[i].get_name(), fld[i].bit_width, val, fld[i].val), UVM_LOW)
      end
      val = val << fld[i].bit_width;
    end
  endfunction

endclass
