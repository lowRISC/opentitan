// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_env_cfg extends cip_base_env_cfg #(.RAL_T(ac_range_check_reg_block));

  // External component config objects
  rand tl_agent_cfg tl_csr_agt_cfg;
  rand tl_agent_cfg tl_unfilt_agt_cfg;
  rand tl_agent_cfg tl_filt_agt_cfg;

  `uvm_object_utils_begin(ac_range_check_env_cfg)
    `uvm_field_object(tl_csr_agt_cfg, UVM_DEFAULT)
    `uvm_field_object(tl_unfilt_agt_cfg, UVM_DEFAULT)
    `uvm_field_object(tl_filt_agt_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void initialize(bit [31:0] csr_base_addr = '1);
endclass : ac_range_check_env_cfg


function ac_range_check_env_cfg::new(string name="");
  super.new(name);
endfunction : new

function void ac_range_check_env_cfg::initialize(bit [31:0] csr_base_addr = '1);
  list_of_alerts = ac_range_check_env_pkg::LIST_OF_ALERTS;
  super.initialize(csr_base_addr);
  // Create tl_csr agent config obj
  tl_csr_agt_cfg = tl_agent_cfg::type_id::create("tl_csr_agt_cfg");
  // Create tl_unfilt agent config obj
  tl_unfilt_agt_cfg = tl_agent_cfg::type_id::create("tl_unfilt_agt_cfg");
  // Create tl_filt agent config obj
  tl_filt_agt_cfg = tl_agent_cfg::type_id::create("tl_filt_agt_cfg");

  // Set num_interrupts
  begin
    uvm_reg rg = ral.get_reg_by_name("intr_state");
    if (rg != null) begin
      num_interrupts = ral.intr_state.get_n_used_bits();
    end
  end
endfunction : initialize
