// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_agent_cfg extends dv_base_agent_cfg;

  virtual entropy_src_xht_if vif;

  bit     start_default_seq = 1'b0;
  bit     unfiltered_monitor_traffic = 1'b0;

  `uvm_object_utils_begin(entropy_src_xht_agent_cfg)
    `uvm_field_int(start_default_seq, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
