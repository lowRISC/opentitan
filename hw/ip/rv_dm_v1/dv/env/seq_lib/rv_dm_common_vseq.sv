// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_common_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_common_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }

  // We set these initial inputs to known values to prevent side effects that may affect these
  // common tests.
  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
  constraint unavailable_c {
    unavailable == 0;
  }

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
