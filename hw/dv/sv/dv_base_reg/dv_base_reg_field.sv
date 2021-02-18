// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register reg class which will be used to generate the reg field
class dv_base_reg_field extends uvm_reg_field;
  local string m_original_access;

  `uvm_object_utils(dv_base_reg_field)
  `uvm_object_new

  // Issue #5105: UVM forces the value member to be non-randomizable for certain access policies.
  // We restore it in this extended class.
  virtual function void configure(uvm_reg        parent,
                                  int unsigned   size,
                                  int unsigned   lsb_pos,
                                  string         access,
                                  bit            volatile,
                                  uvm_reg_data_t reset,
                                  bit            has_reset,
                                  bit            is_rand,
                                  bit            individually_accessible);
      super.configure(.parent   (parent),
                      .size     (size),
                      .lsb_pos  (lsb_pos),
                      .access   (access),
                      .volatile (volatile),
                      .reset    (reset),
                      .has_reset(has_reset),
                      .is_rand  (is_rand),
                      .individually_accessible(individually_accessible));
      value.rand_mode(is_rand);
    endfunction

  // when use UVM_PREDICT_WRITE and the CSR access is WO, this function will return the default
  // val of the register, rather than the written value
  virtual function uvm_reg_data_t XpredictX(uvm_reg_data_t cur_val,
                                            uvm_reg_data_t wr_val,
                                            uvm_reg_map map);

    if (get_access(map) == "WO") return get_reset();
    else return super.XpredictX(cur_val, wr_val, map);
  endfunction

  virtual function string get_original_access();
    return m_original_access;
  endfunction

  virtual function void set_original_access(string access);
    if (m_original_access == "") begin
      m_original_access = access;
    end else begin
      `uvm_fatal(`gfn, "register original access can only be written once")
    end
  endfunction

  virtual function void set_locked_fields_access(string access = "original_access");
    case (access)
      "RO": void'(this.set_access(access));
      "original_access": void'(this.set_access(m_original_access));
      default: `uvm_fatal(`gfn, $sformatf("attempt to set access to %s", access))
    endcase
  endfunction

endclass
