// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_soc_proxy_smoke_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_soc_proxy_smoke_vseq)

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    // We want to control the SoC external reset request signal directly.
    cfg.monitor_internal_resets = 1'b0;
    super.dut_init();
  endtask

  virtual task body();
    super.body();

    // Wait until SW reaches the test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "External resets enabled.")

    // Fork background threads to ensure that most reset domains do *not* get reset.
    fork
      begin
        cfg.chip_vif.io_clk_rst_if.wait_for_reset(.wait_negedge(1), .wait_posedge(0));
        `dv_error("IO reset domain asserted when it should not!")
      end
      begin
        cfg.chip_vif.aon_clk_por_rst_if.wait_for_reset(.wait_negedge(1), .wait_posedge(0));
        `dv_error("POR reset domain asserted when it should not!")
      end
    join_none

    // Ensure that the desired reset domains get cycled now.
    `DV_SPINWAIT_EXIT(
      // Wait threads: wait until all desired reset domains have been cycled.
      fork
        begin
          // Trigger the external reset request; note that because of synchronization delays and
          // 4-cycle filtering (on both assertion and deassertion) we need to allow circa 12
          // additional cycles before the 32-cycle timeout below.
          int unsigned clks = $urandom_range(18, 5);
          `uvm_info(`gfn, $sformatf("Applying SoC reset request for %0d cycle(s)", clks),
                    UVM_MEDIUM)
          apply_soc_reset_request(clks);
        end
        begin
          cfg.chip_vif.cpu_clk_rst_if.wait_for_reset();
          `uvm_info(`gfn, $sformatf("CPU reset cycled."), UVM_LOW)
        end
      join
      ,
      // Exit thread: allow at most 20 AON clock cycles until the above domains must reset, but it
      // may take 12 cycles for the reset to be seen within the DUT; see above.
      cfg.chip_vif.aon_clk_por_rst_if.wait_clks(32);
      `dv_error("Resets did not complete within required time!")
    )

  endtask

endclass
