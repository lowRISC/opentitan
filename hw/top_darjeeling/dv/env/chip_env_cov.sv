// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_alert_cg_wrap;
  // This covergroup samples alerts triggered.
  covergroup alert_cg(string name) with function sample (bit triggered);
    option.name = name;
    option.per_instance = 1;

    // It is only interesting when the alert was actually triggered.
    triggered_cp: coverpoint triggered {
       ignore_bins ignore = {0};
    }
  endgroup

  function new(string name);
     alert_cg = new(name);
  endfunction

  function void sample(bit triggered);
    alert_cg.sample(triggered);
  endfunction
endclass

class chip_env_cov extends cip_base_env_cov #(.CFG_T(chip_env_cfg));
  `uvm_component_utils(chip_env_cov)

  // the base class provides the following handles for use:
  // chip_env_cfg: cfg

  // covergroups
  chip_alert_cg_wrap alert_cg_wrap[NUM_ALERTS];

  function new(string name, uvm_component parent);
    super.new(name, parent);

    // instantiate all covergroups here
    `uvm_info(`gfn, $sformatf("Instantiating %0d alert_cg wrappers", NUM_ALERTS), UVM_MEDIUM)
    foreach (alert_cg_wrap[i]) begin
      alert_cg_wrap[i] = new(LIST_OF_ALERTS[i]);
    end
  endfunction : new

endclass
