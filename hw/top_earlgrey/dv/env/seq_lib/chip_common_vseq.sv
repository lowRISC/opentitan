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

    // In top-level uart RX pin may be selected in pinmux. CSR tests may randomly enable line
    // loopback, which will connect TX with RX. If RX isn't enabled in pinmux, it will be 0.
    // moniter will start to check the TX data when it changes from 1 to 0. But the length of 0 may
    // be not right in CSR test.
    // In block-level, we always ties RX to 1 (idle) in CSR test. No need to disable the monitor
    cfg.m_uart_agent_cfg.en_tx_monitor = 0;
  endtask

  task post_start();
    super.post_start();
    // Random CSR rw might trigger alert. Some alerts will conintuously be triggered until reset
    // applied, which will cause alert_monitor phase_ready_to_end timeout.
    apply_reset();
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    // Backdoor load the OTP image.
    cfg.otp_bkdr_vif.load_mem_from_file({cfg.sw_images[SwTypeOtp], ".vmem"});
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
