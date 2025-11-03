// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_common_vseq extends ${module_instance_name}_base_vseq;
  `uvm_object_utils(${module_instance_name}_common_vseq)
  extern function new (string name="");

  extern constraint num_trans_c;

  extern task body();
endclass : ${module_instance_name}_common_vseq

function ${module_instance_name}_common_vseq::new (string name = "");
  super.new(name);
endfunction

constraint ${module_instance_name}_common_vseq::num_trans_c {
  num_trans inside {[1:2]};
}

task ${module_instance_name}_common_vseq::body();
  run_common_vseq_wrapper(num_trans);
endtask
