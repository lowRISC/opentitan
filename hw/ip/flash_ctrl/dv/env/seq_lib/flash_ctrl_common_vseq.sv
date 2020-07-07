// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_common_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_common_vseq)

  `uvm_object_new

  virtual function void configure_vseq();
    cfg.seq_cfg.max_num_trans = 2;
  endfunction

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
