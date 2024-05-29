// Copyright lowRISC contributors (OpenTitan project).
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

  // This is a thin wrapper around the base class version of run_csr_vseq, but setting the timeout
  // for the CSR operations to be larger. This is needed because the timeout counts from (roughly)
  // the start of the CSR sequence and isn't enough to allow for slow values of the JTAG clock.
  virtual task run_csr_vseq(string csr_test_type,
                            int    num_test_csrs = 0,
                            bit    do_rand_wr_and_reset = 1,
                            dv_base_reg_block models[$] = {},
                            string ral_name = "");
    uint old_dtn = csr_utils_pkg::default_timeout_ns;

    csr_utils_pkg::default_timeout_ns = 10 * old_dtn;
    super.run_csr_vseq(csr_test_type, num_test_csrs, do_rand_wr_and_reset, models, ral_name);
    csr_utils_pkg::default_timeout_ns = old_dtn;
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
