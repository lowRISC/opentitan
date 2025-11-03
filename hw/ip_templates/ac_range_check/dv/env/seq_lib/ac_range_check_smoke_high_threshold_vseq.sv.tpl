// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_smoke_high_threshold_vseq extends ${module_instance_name}_smoke_vseq;
  import ${module_instance_name}_reg_pkg::*;
  `uvm_object_utils(${module_instance_name}_smoke_high_threshold_vseq)

  // Constraints
  extern constraint range_attr_c;
  extern constraint deny_cnt_threshold_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : ${module_instance_name}_smoke_high_threshold_vseq

constraint ${module_instance_name}_smoke_high_threshold_vseq::range_attr_c {
  foreach (dut_cfg.range_base[i]) {
    dut_cfg.range_attr[i].execute_access dist {
      0 :/ 9,
      1 :/ 1
    };
    dut_cfg.range_attr[i].write_access dist {
      0 :/ 9,
      1 :/ 1
    };
    dut_cfg.range_attr[i].read_access dist {
      0 :/ 9,
      1 :/ 1
    };
    dut_cfg.range_attr[i].enable dist {
      0 :/ 9,
      1 :/ 1
    };
  }
}

constraint ${module_instance_name}_smoke_high_threshold_vseq::deny_cnt_threshold_c {
  if (apply_deny_cnt_threshold_c) {
    deny_cnt_threshold inside {[(1 << DenyCountWidth)-6 : (1 << DenyCountWidth)-1]};
  } else {
    deny_cnt_threshold == fixed_deny_cnt_threshold;
  }
}

function ${module_instance_name}_smoke_high_threshold_vseq::new(string name="");
  super.new(name);
endfunction : new

task ${module_instance_name}_smoke_high_threshold_vseq::body();
  super.body();
endtask : body
