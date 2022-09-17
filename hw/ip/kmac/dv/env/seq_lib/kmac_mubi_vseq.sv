// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_mubi_vseq extends kmac_app_vseq;

  `uvm_object_utils(kmac_mubi_vseq)
  `uvm_object_new

  constraint en_app_c {
    en_app dist {
      0 :/ 1,
      1 :/ 1
    };
  }

  virtual task kmac_init(bit wait_init = 1, bit keymgr_app_intf = 0);
    string sha3_done_path = "tb.dut.sha3_done";
    string sha3_absorbed_path = "tb.dut.sha3_absorbed";
    super.kmac_init(wait_init, keymgr_app_intf);
    // Randomly deposit mubi values to values other than mubi_true.
    `DV_CHECK_FATAL(
        uvm_hdl_deposit(sha3_done_path, get_rand_mubi4_val(.t_weight(0), .f_weight(0))))
    `DV_CHECK_FATAL(
        uvm_hdl_deposit(sha3_absorbed_path, get_rand_mubi4_val(.t_weight(0), .f_weight(0))))
  endtask

endclass
