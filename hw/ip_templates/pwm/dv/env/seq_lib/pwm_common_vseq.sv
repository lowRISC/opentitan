// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_common_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_common_vseq)
  extern function new (string name="");

  extern constraint num_trans_c;

  extern task body();
endclass : pwm_common_vseq

function pwm_common_vseq::new (string name = "");
  super.new(name);
endfunction

constraint pwm_common_vseq::num_trans_c {
  num_trans inside {[1:2]};
}

task pwm_common_vseq::body();
  run_common_vseq_wrapper(num_trans);
endtask
