// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_common_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new


  virtual task pre_start();
    do_aes_init = 1'b0;
    super.pre_start();
    cfg.en_scb = 0;
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
