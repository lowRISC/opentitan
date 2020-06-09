// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register class which will be used to generate the reg
class dv_base_reg extends uvm_reg;
  // external reg doesn't have storage in reg module, which may connect to some combinational logic
  // hence, backdoor write isn't available
  local bit is_ext_reg;

  local dv_base_reg locked_regs[$];

  function new(string       name = "",
               int unsigned n_bits,
               int          has_coverage);
    super.new(name, n_bits, has_coverage);
  endfunction : new

  function void get_dv_base_reg_fields(ref dv_base_reg_field dv_fields[$]);
    uvm_reg_field ral_fields[$];
    get_fields(ral_fields);
    foreach (ral_fields[i]) `downcast(dv_fields[i], ral_fields[i])
  endfunction

  // get_n_bits will return number of all the bits in the csr
  // while this function will return actual number of bits used in reg field
  function uint get_n_used_bits();
    uvm_reg_field fields[$];
    get_fields(fields);
    foreach (fields[i]) get_n_used_bits += fields[i].get_n_bits();
  endfunction

  // loop all the fields to find the msb position of this reg
  function uint get_msb_pos();
    uvm_reg_field fields[$];
    get_fields(fields);
    foreach (fields[i]) begin
      uint field_msb_pos = fields[i].get_lsb_pos() + fields[i].get_n_bits() - 1;
      if (field_msb_pos > get_msb_pos) get_msb_pos = field_msb_pos;
    end
  endfunction

  // if the register is an enable reg, it will add controlled registers in the queue
  function void add_locked_reg(dv_base_reg locked_reg);
    locked_regs.push_back(locked_reg);
  endfunction

  function bit is_enable_reg();
    return (locked_regs.size() > 0);
  endfunction

  // if enable register is set to 1, the locked registers will be set to RO access
  // once enable register is reset to 0, the locked registers will be set back to original access
  function void set_locked_regs_access(string access = "original_access");
    foreach (locked_regs[i]) begin
      dv_base_reg_field locked_fields[$];
      locked_regs[i].get_dv_base_reg_fields(locked_fields);
      foreach (locked_fields[i]) locked_fields[i].set_locked_fields_access(access);
    end
  endfunction

  function void get_locked_regs(ref dv_base_reg locked_regs_q[$]);
    locked_regs_q = locked_regs;
  endfunction

  // post_write callback to handle reg enables
  // TODO: create an `enable_field_access_policy` variable and set the template code during
  // automation.
  virtual task post_write(uvm_reg_item rw);
    dv_base_reg_field fields[$];
    string field_access;
    if (is_enable_reg()) begin
      get_dv_base_reg_fields(fields);
      field_access = fields[0].get_access();
      case (field_access)
        // rw.value is a dynamic array
        "W1C": if (rw.value[0][0] == 1'b1) set_locked_regs_access("RO");
        "W0C": if (rw.value[0][0] == 1'b0) set_locked_regs_access("RO");
        "RO": ; // if RO, it's updated by design, need to predict in scb
        default:`uvm_fatal(`gtn, $sformatf("enable register invalid access %s", field_access))
      endcase
    end
  endtask

  virtual function void set_is_ext_reg(bit is_ext);
    is_ext_reg = is_ext;
  endfunction

  virtual function bit get_is_ext_reg();
    return is_ext_reg;
  endfunction

endclass
