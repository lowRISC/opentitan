// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run the JTAG DMT CSRs through our standard CSR suite via JTAG.
class rv_dm_jtag_dtm_csr_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_csr_vseq)
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
    run_csr_vseq_wrapper(.num_times(num_trans), .models({jtag_dtm_ral}));
 endtask : body

endclass
