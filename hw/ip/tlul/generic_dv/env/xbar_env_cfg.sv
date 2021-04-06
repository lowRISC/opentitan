// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment configuration class
// ---------------------------------------------
class xbar_env_cfg extends dv_base_env_cfg;

  rand tl_agent_cfg  host_agent_cfg[];
  rand tl_agent_cfg  device_agent_cfg[];
  uint               num_hosts;
  uint               num_devices;
  uint               num_enabled_hosts;
  // Actual number of a_source bits used by the design.
  uint               valid_a_source_width;
  // enable to drop valid without ready
  rand bit           allow_host_drop_valid_wo_ready;
  rand bit           allow_device_drop_valid_wo_ready;
  uint               min_host_valid_len   = 1;
  uint               max_host_valid_len   = 50;
  uint               min_device_valid_len = 1;
  uint               max_device_valid_len = 50;
  // delays for TL transaction
  uint               min_host_req_delay   = 0;
  uint               max_host_req_delay   = 20;
  uint               min_host_rsp_delay   = 0;
  uint               max_host_rsp_delay   = 20;
  uint               min_device_req_delay = 0;
  uint               max_device_req_delay = 20;
  uint               min_device_rsp_delay = 0;
  uint               max_device_rsp_delay = 20;

  `uvm_object_utils_begin(xbar_env_cfg)
    `uvm_field_array_object(host_agent_cfg,    UVM_DEFAULT)
    `uvm_field_array_object(device_agent_cfg,  UVM_DEFAULT)
    `uvm_field_int(num_hosts,                  UVM_DEFAULT)
    `uvm_field_int(num_devices,                UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    is_initialized = 1'b1;
    ral_model_names = {}; // no csr in xbar
    // Host TL agent cfg
    num_hosts             = xbar_hosts.size();
    num_enabled_hosts     = xbar_hosts.size();
    valid_a_source_width  = top_pkg::TL_AIW - $clog2(num_hosts);
    host_agent_cfg        = new[num_hosts];
    foreach (host_agent_cfg[i]) begin
      host_agent_cfg[i]   = tl_agent_cfg::type_id::
                            create($sformatf("%0s_agent_cfg", xbar_hosts[i].host_name));
      host_agent_cfg[i].if_mode = dv_utils_pkg::Host;
      host_agent_cfg[i].valid_a_source_width = valid_a_source_width;
      host_agent_cfg[i].max_outstanding_req = 1 << valid_a_source_width;
      host_agent_cfg[i].host_can_stall_rsp_when_a_valid_high = $urandom_range(0, 1);
    end
    // Device TL agent cfg
    num_devices      = xbar_devices.size();
    device_agent_cfg = new[num_devices];
    foreach (device_agent_cfg[i]) begin
      device_agent_cfg[i] = tl_agent_cfg::type_id::
                            create($sformatf("%0s_agent_cfg", xbar_devices[i].device_name));
      device_agent_cfg[i].if_mode = dv_utils_pkg::Device;
      device_agent_cfg[i].allow_d_valid_drop_wo_d_ready = allow_device_drop_valid_wo_ready;
      // the max_outstanding_req depends on how many hosts can access the device
      // device.max_outstanding_req = sum(all its hosts max_outstanding_req)
      device_agent_cfg[i].max_outstanding_req = 0; // clear default value
      foreach (xbar_hosts[j]) begin
        if (xbar_devices[i].device_name inside {xbar_hosts[j].valid_devices}) begin
          device_agent_cfg[i].max_outstanding_req += host_agent_cfg[j].max_outstanding_req;
        end
      end // foreach (xbar_hosts[j])
    end // foreach (device_agent_cfg[i])
  endfunction

  // update TLUL agent cfg according to this env cfg. These values may be updated in test
  virtual function void update_agent_cfg();
    foreach (host_agent_cfg[i]) begin
      host_agent_cfg[i].allow_a_valid_drop_wo_a_ready = allow_host_drop_valid_wo_ready;
      host_agent_cfg[i].a_valid_len_min   = min_host_valid_len;
      host_agent_cfg[i].a_valid_len_max   = max_host_valid_len;
      host_agent_cfg[i].a_valid_delay_min = min_host_req_delay;
      host_agent_cfg[i].a_valid_delay_max = max_host_req_delay;
      host_agent_cfg[i].d_ready_delay_min = min_host_rsp_delay;
      host_agent_cfg[i].d_ready_delay_max = max_host_rsp_delay;
    end
    foreach (device_agent_cfg[i]) begin
      device_agent_cfg[i].allow_d_valid_drop_wo_d_ready = allow_device_drop_valid_wo_ready;
      device_agent_cfg[i].d_valid_len_min   = min_device_valid_len;
      device_agent_cfg[i].d_valid_len_max   = max_device_valid_len;
      device_agent_cfg[i].d_valid_delay_min = min_device_req_delay;
      device_agent_cfg[i].d_valid_delay_max = max_device_req_delay;
      device_agent_cfg[i].a_ready_delay_min = min_device_rsp_delay;
      device_agent_cfg[i].a_ready_delay_max = max_device_rsp_delay;
    end
  endfunction
endclass
