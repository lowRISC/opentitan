// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_common_vseq extends chip_base_vseq;
  `uvm_object_utils(chip_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    // Select SPI interface.
    cfg.jtag_spi_n_vif.drive(1'b0);
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    // TODO rstmgr takes some time to release reset for IPs. Need to find a better way to know when
    // reset is released by rstmgr
    cfg.clk_rst_vif.wait_clks(100);
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass

`undef add_ip_csr_exclusions
