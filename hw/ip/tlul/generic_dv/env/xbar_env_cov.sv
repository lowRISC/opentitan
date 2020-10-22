// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// sample at xbar_access_same_device_vseq
covergroup same_device_access_cg (uint num_dev) with function sample(uint dev_id);
  cp_dev: coverpoint dev_id {
    bins all_values[] = {[0:num_dev-1]};
    illegal_bins bin_others = default;
  }
endgroup

// sample at xbar_same_source_vseq
covergroup same_source_access_cg (uint num_source) with function sample(uint source);
  cp_dev: coverpoint source {
    bins all_values[] = {[0:num_source-1]};
    illegal_bins bin_others = default;
  }
endgroup

// wrap covergroup as a class to use it as an associative array
// sample at xbar_env_cov::build_phase
class max_delay_cg_obj;

  covergroup max_delay_cg (string name) with function sample(uint req_dly, uint rsp_dly);
    option.per_instance = 1;
    option.name = name;
    cp_req_dly: coverpoint req_dly {
      bins zero        = {0};
      bins small_delay = {[1:20]};
      bins big_delay   = {[100:1000]};
    }
    cp_rsp_dly: coverpoint rsp_dly {
      bins zero        = {0};
      bins small_delay = {[1:20]};
      bins big_delay   = {[100:1000]};
    }
  endgroup

  function new(string name = "");
    max_delay_cg = new(name);
  endfunction : new

  function void sample(uint req_dly, uint rsp_dly);
    max_delay_cg.sample(req_dly, rsp_dly);
  endfunction : sample
endclass : max_delay_cg_obj

class xbar_env_cov extends dv_base_env_cov #(.CFG_T(xbar_env_cfg));
  same_device_access_cg   same_device_access_cg;
  same_source_access_cg   same_source_access_cg;
  // cover mapped/unmapped addr per host
  bit_toggle_cg_wrap      host_access_mapped_addr_cg[string];
  // cover max_delay per host/device
  max_delay_cg_obj        max_delay_cg_obj[string];
  `uvm_component_utils(xbar_env_cov)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    same_device_access_cg = new(cfg.num_devices);
    same_source_access_cg = new(1 << cfg.valid_a_source_width);
    foreach (xbar_hosts[i]) begin
      host_access_mapped_addr_cg[xbar_hosts[i].host_name] = new(xbar_hosts[i].host_name);
      max_delay_cg_obj[xbar_hosts[i].host_name]           = new(xbar_hosts[i].host_name);
      max_delay_cg_obj[xbar_hosts[i].host_name].sample(cfg.max_host_req_delay,
                                                       cfg.max_host_rsp_delay);
    end
    foreach (xbar_devices[i]) begin
      max_delay_cg_obj[xbar_devices[i].device_name] = new(xbar_devices[i].device_name);
      max_delay_cg_obj[xbar_devices[i].device_name].sample(cfg.max_device_req_delay,
                                                           cfg.max_device_rsp_delay);
    end
  endfunction

endclass
