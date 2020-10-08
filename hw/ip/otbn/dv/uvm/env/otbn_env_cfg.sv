// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_env_cfg extends cip_base_env_cfg #(.RAL_T(otbn_reg_block));

  // ext component cfgs

  `uvm_object_utils_begin(otbn_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new


  function void initialize(bit [31:0] csr_base_addr = '1);
    // Tell the CIP base code not to look for a "devmode" interface. OTBN doesn't have one.
    has_devmode = 0;

    // Set the list of alerts, needed by the CIP base code. This needs to match the names assigned
    // in tb.sv (where we bind in the alert interfaces and register each with the UVM DB). Rather
    // than copying the names out of the hjson, we're just referencing them by number for now.
    list_of_alerts = new[NumAlerts];
    for (int i = 0; i < NumAlerts; i++) begin
      list_of_alerts[i] = $sformatf("%0d", i);
    end

    super.initialize(csr_base_addr);
  endfunction

endclass
