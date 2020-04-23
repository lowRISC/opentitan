// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// override tl_seq_item with xbar_seq_err_item to disable TL protocol related constraint
class xbar_error_test extends xbar_base_test;
  `uvm_component_utils(xbar_error_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tl_seq_item::type_id::set_type_override(xbar_seq_err_item::get_type());
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    // disable assertions for TL errors
    uvm_config_db#(bit)::set(null, "*", "tlul_assert_en", 0);
    super.run_phase(phase);
  endtask : run_phase
endclass : xbar_error_test
