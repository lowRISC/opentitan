// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rv_core_ibex_icache_invalidate_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rv_core_ibex_icache_invalidate_vseq)

  `uvm_object_new

  virtual task body();
    super.body();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    // Wait for rv_core_ibex.icache_otp_key_o.req then rv_core_ibex.icache_otp_key_i.ack to become
    // high, which indicates a completed icache scramble key exchange.
    `DV_WAIT(cfg.chip_vif.rv_core_ibex_icache_otp_key_req == 1'b1)
    `DV_WAIT(cfg.chip_vif.rv_core_ibex_icache_otp_key_ack == 1'b1)

    // Wait for the core to signal completion of the icache invalidation by completing the test
    // program.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusPassed)

    // Give assertions a few cycles to conclude.  If they don't fail until then, the test passes.
    cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(100);
  endtask

endclass
