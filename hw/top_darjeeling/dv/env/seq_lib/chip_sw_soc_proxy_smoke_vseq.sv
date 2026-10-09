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

    // Ensure that the desired reset domains get their reset asserted promptly.
    `DV_SPINWAIT_EXIT(
      // Wait threads: apply the reset request and observe the CPU reset assertion.
      fork
        begin
          // Trigger the external reset request; note that because of synchronization delays and
          // 4-cycle filtering (on both assertion and deassertion) we need to allow circa 12
          // additional cycles for the request to be seen within the DUT.
          int unsigned clks = $urandom_range(18, 5);
          `uvm_info(`gfn, $sformatf("Applying SoC reset request for %0d cycle(s)", clks),
                    UVM_MEDIUM)
          apply_soc_reset_request(clks);
        end
        begin
          cfg.chip_vif.cpu_clk_rst_if.wait_for_reset(.wait_negedge(1), .wait_posedge(0));
          `uvm_info(`gfn, "CPU reset asserted.", UVM_LOW)
        end
      join
      ,
      // Exit thread: apply_soc_reset_request() takes up to 2 * 18 AON clock cycles, and the reset
      // asserts circa 12 cycles after the request.
      cfg.chip_vif.aon_clk_por_rst_if.wait_clks(64);
      `dv_error("Reset was not asserted within required time!")
    )

    // The pwrmgr keeps the CPU in reset until the SoC acknowledges, and the base vseq's
    // acknowledger is disabled here. Acknowledge once the request has dropped inside the pwrmgr,
    // or the pwrmgr re-arms ext_rst_pending.
    `DV_SPINWAIT_EXIT(
      do cfg.chip_vif.aon_clk_por_rst_if.wait_clks(1);
      while (cfg.chip_vif.signal_probe_pwrmgr_light_reset_req(
             .kind(dv_utils_pkg::SignalProbeSample)));
      ,
      cfg.chip_vif.aon_clk_por_rst_if.wait_clks(64);
      `dv_error("SoC reset request was not deasserted within required time!")
    )
    apply_soc_reset_ack();

    // The pwrmgr releases the resets a few cycles after the acknowledgment.
    `DV_SPINWAIT_EXIT(
      cfg.chip_vif.cpu_clk_rst_if.wait_for_reset(.wait_negedge(0), .wait_posedge(1));
      `uvm_info(`gfn, "CPU reset cycled.", UVM_LOW)
      ,
      cfg.chip_vif.aon_clk_por_rst_if.wait_clks(1000);
      `dv_error("Reset was not released within required time!")
    )

  endtask

endclass
