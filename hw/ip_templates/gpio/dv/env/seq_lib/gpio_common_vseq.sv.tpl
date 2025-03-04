// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_common_vseq extends ${module_instance_name}_base_vseq;
  `uvm_object_utils(${module_instance_name}_common_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:3]};
  }

  virtual task dut_init(string reset_kind = "HARD");
    // Implement gpio pulldown for csr tests for avoiding comparison
    // mismatch for DATA_IN register checks
    set_gpio_pulls(.pu(1'b0), .pd(1'b1));
    super.dut_init(reset_kind);
  endtask: dut_init

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
