// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence enable random classes, and rand wr phase cycles

class ${module_instance_name}_random_classes_vseq extends ${module_instance_name}_random_alerts_vseq;
  `uvm_object_utils(${module_instance_name}_random_classes_vseq)

  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    this.enable_classa_only_c.constraint_mode(0);
  endfunction

endclass : ${module_instance_name}_random_classes_vseq
