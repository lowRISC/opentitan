// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_common_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task body();
    // Enable access to debug ROM for the common sequences to work.
    // TODO (lowrisc/opentitan/#10453): Figure out if this needs to be mdified based on the common
    // test seq that is run.
    cfg.rv_dm_vif.lc_hw_debug_en = lc_ctrl_pkg::On;
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
