// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_common_vseq extends ${module_instance_name}_base_vseq;
  `uvm_object_utils(${module_instance_name}_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    fork
      super.body();
      run_common_vseq_wrapper(num_trans);
    join
  endtask : body

endclass
