// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_rv_core_ibex_icache_invalidate_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rv_core_ibex_icache_invalidate_vseq)

  `uvm_object_new

  import dv_utils_pkg::SignalProbeSample;

  task await_icache_inval();
    // Wait for rv_core_ibex.icache_otp_key_o.req then rv_core_ibex.icache_otp_key_i.ack to become
    // high, which indicates a completed icache scramble key exchange.
    `DV_WAIT(cfg.chip_vif.rv_core_ibex_icache_otp_key_req == 1'b1)
    `DV_WAIT(cfg.chip_vif.rv_core_ibex_icache_otp_key_ack == 1'b1)

    // Wait for both signals to become low again, so the next key exchange can be observed.
    `DV_WAIT(cfg.chip_vif.rv_core_ibex_icache_otp_key_req == 1'b0)
    `DV_WAIT(cfg.chip_vif.rv_core_ibex_icache_otp_key_ack == 1'b0)
  endtask

  virtual task body();
    int unsigned num_icache_invals = 0;

    super.body();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    fork
      begin
        // Count number of completed icache invalidations.  This thread is meant to not stop until
        // it is killed after the completion of the second thread (which can time out, so this is
        // never an infinite loop).
        forever begin
          await_icache_inval();
          num_icache_invals++;
        end
      end
      begin
        // Wait for the core to signal completion of the icache invalidations by completing the test
        // program.  If the core does not signal completion, the enclosing fork will not join and
        // the test will time out.
        `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusPassed)
      end
    join_any
    disable fork;

    // We expect the core to perform 7 icache invalidations.  (This number has to be kept in sync
    // with the C code).
    `DV_CHECK_EQ(num_icache_invals, 7, "Unexpected number of icache invalidations")

    // Give assertions a few cycles to conclude.  If they don't fail until then, the test passes.
    cfg.chip_vif.cpu_clk_rst_if.wait_n_clks(100);
  endtask

endclass
