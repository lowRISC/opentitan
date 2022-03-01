// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_common_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
  endtask : dut_init

  virtual task body();
    do_sysrst_ctrl_init = 1'b0;
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
