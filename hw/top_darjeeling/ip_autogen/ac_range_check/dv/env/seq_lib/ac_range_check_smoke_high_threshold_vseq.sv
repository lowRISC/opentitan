// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_smoke_high_threshold_vseq extends ac_range_check_smoke_vseq;
  import ac_range_check_reg_pkg::*;
  `uvm_object_utils(ac_range_check_smoke_high_threshold_vseq)

  // Constraints
  extern constraint range_attr_c;
  extern constraint deny_cnt_threshold_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : ac_range_check_smoke_high_threshold_vseq

constraint ac_range_check_smoke_high_threshold_vseq::range_attr_c {
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

constraint ac_range_check_smoke_high_threshold_vseq::deny_cnt_threshold_c {
  if (apply_deny_cnt_threshold_c) {
    deny_cnt_threshold inside {[(1 << DenyCountWidth)-6 : (1 << DenyCountWidth)-1]};
  } else {
    deny_cnt_threshold == fixed_deny_cnt_threshold;
  }
}

function ac_range_check_smoke_high_threshold_vseq::new(string name="");
  super.new(name);
endfunction : new

task ac_range_check_smoke_high_threshold_vseq::body();
  super.body();
endtask : body
