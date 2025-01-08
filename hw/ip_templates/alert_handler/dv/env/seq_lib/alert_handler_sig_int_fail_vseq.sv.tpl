// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence enable signal intergrity fail.

class ${module_instance_name}_sig_int_fail_vseq extends ${module_instance_name}_smoke_vseq;
  `uvm_object_utils(${module_instance_name}_sig_int_fail_vseq)

  `uvm_object_new

  constraint esc_accum_thresh_c {
    foreach (accum_thresh[i]) {accum_thresh[i] dist {[0:1] :/ 5, [2:10] :/ 5};}
  }

  function void pre_randomize();
    this.enable_one_alert_c.constraint_mode(0);
    this.enable_classa_only_c.constraint_mode(0);
    this.sig_int_c.constraint_mode(0);
  endfunction

endclass : ${module_instance_name}_sig_int_fail_vseq
