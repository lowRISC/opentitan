// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// tl_agent environment configuration class
// ---------------------------------------------
class tl_agent_env_cfg extends dv_base_env_cfg;

  rand tl_agent_cfg  host_agent_cfg;
  rand tl_agent_cfg  device_agent_cfg;

  `uvm_object_utils_begin(tl_agent_env_cfg)
    `uvm_field_object(host_agent_cfg,    UVM_DEFAULT)
    `uvm_field_object(device_agent_cfg,  UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    has_ral = 0; // no csr in tl_agent
    host_agent_cfg = tl_agent_cfg::type_id::create("host_agent_cfg");
    host_agent_cfg.max_outstanding_req = 1 << SourceWidth;
    host_agent_cfg.if_mode = dv_utils_pkg::Host;

    device_agent_cfg = tl_agent_cfg::type_id::create("device_agent_cfg");
    device_agent_cfg.if_mode = dv_utils_pkg::Device;
    device_agent_cfg.max_outstanding_req = 1 << SourceWidth;
    device_agent_cfg.device_can_rsp_on_same_cycle = 1;
  endfunction

endclass
