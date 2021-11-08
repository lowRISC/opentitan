// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_in_out_passthrough_seq extends sysrst_ctrl_base_seq;
  
  `uvm_object_utils(sysrst_ctrl_in_out_passthrough_seq)

  `uvm_object_new

   sysrst_ctrl_item data_item;

  virtual task body();
     data_item = sysrst_ctrl_item::type_id::create("data_item");
  
     start_item(data_item);
     assert(data_item.randomize());
     finish_item(data_item);
     
  endtask

endclass
