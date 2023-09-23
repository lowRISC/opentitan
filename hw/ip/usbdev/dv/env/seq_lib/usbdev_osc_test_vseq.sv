// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// csr reset and read/write test vseq
class usbdev_osc_test_vseq extends usbdev_common_vseq;
  `uvm_object_utils(usbdev_osc_test_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t data;
    csr_wr(.ptr(ral.phy_config.tx_osc_test_mode), .value(1));
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 200));

  endtask : body

endclass //: usbdev_osc_test_vseq
