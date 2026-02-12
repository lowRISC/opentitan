// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_smoke_racl_vseq extends ${module_instance_name}_smoke_vseq;
  `uvm_object_utils(${module_instance_name}_smoke_racl_vseq)

  // Constraints
  extern constraint range_attr_c;
  extern constraint range_racl_policy_c;

  // Standard SV/UVM methods
  extern function new(string name="");
endclass : ${module_instance_name}_smoke_racl_vseq


constraint ${module_instance_name}_smoke_racl_vseq::range_attr_c {
  foreach (dut_cfg.range_base[i]) {
    dut_cfg.range_attr[i].execute_access == 1;
    dut_cfg.range_attr[i].write_access   == 1;
    dut_cfg.range_attr[i].read_access    == 1;
    dut_cfg.range_attr[i].enable dist {
      0 :/ 1,
      1 :/ 2
    };
  }
}

constraint ${module_instance_name}_smoke_racl_vseq::range_racl_policy_c {
  foreach (dut_cfg.range_racl_policy[i]) {
    dut_cfg.range_racl_policy[i].write_perm inside {[16'h0000:16'hFFFF]};
    dut_cfg.range_racl_policy[i].read_perm  inside {[16'h0000:16'hFFFF]};
  }
}

function ${module_instance_name}_smoke_racl_vseq::new(string name="");
  super.new(name);
endfunction : new
