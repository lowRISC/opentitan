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
    enable_asserts_in_hw_reset_rand_wr = 0;
  endtask

  task post_start();
    super.post_start();
    // Random CSR rw might trigger alert. Some alerts will conintuously be triggered until reset
    // applied, which will cause alert_monitor phase_ready_to_end timeout.
    apply_reset();
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    cfg.mem_bkdr_vifs[Otp].clear_mem();
    wait (cfg.rst_n_mon_vif.pins[0] === 1);
    cfg.clk_rst_vif.wait_clks(100);
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    // make sure jtag rst triggers
    cfg.jtag_spi_n_vif.drive(1'b1);
    super.dut_init(reset_kind);
    cfg.jtag_spi_n_vif.drive(1'b0);
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass

`undef add_ip_csr_exclusions
