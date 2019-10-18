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

class xbar_env_cov extends dv_base_env_cov #(.CFG_T(xbar_env_cfg));
  same_device_access_cg   same_device_access_cg;
  same_source_access_cg   same_source_access_cg;
  // cover mapped/unmapped addr per host
  dv_base_generic_cov_obj host_access_mapped_addr_cg[string];
  `uvm_component_utils(xbar_env_cov)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    same_device_access_cg = new(cfg.num_devices);
    same_source_access_cg = new(1 << VALID_HOST_ID_WIDTH);
    foreach (xbar_hosts[i]) begin
      host_access_mapped_addr_cg[xbar_hosts[i].host_name] = new(xbar_hosts[i].host_name);
    end
  endfunction

endclass
