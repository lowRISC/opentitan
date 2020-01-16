// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register reg class which will be used to generate the reg field
class dv_base_reg_field extends uvm_reg_field;
  `uvm_object_utils(dv_base_reg_field)
  `uvm_object_new

  // when use UVM_PREDICT_WRITE and the CSR access is WO, this function will return the default
  // val of the register, rather than the written value
  virtual function uvm_reg_data_t XpredictX(uvm_reg_data_t cur_val,
                                            uvm_reg_data_t wr_val,
                                            uvm_reg_map map);

    if (get_access(map) == "WO") return cur_val;
    else return super.XpredictX(cur_val, wr_val, map);
  endfunction

endclass
