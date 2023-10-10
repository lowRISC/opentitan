// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_soc_proxy_smoke_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_soc_proxy_smoke_vseq)

  `uvm_object_new

  virtual task body();
    super.body();

    // Wait until SW reaches the test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "External resets enabled.")

    // Trigger the external reset request.
    cfg.chip_vif.signal_probe_soc_rst_req_async(.kind(dv_utils_pkg::SignalProbeForce),
                                                .value(1'b1));

    // Fork background threads to ensure that most reset domains do *not* get reset.
    fork
      begin
        cfg.chip_vif.io_div4_clk_rst_if.wait_for_reset(.wait_negedge(1), .wait_posedge(0));
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
          cfg.chip_vif.cpu_clk_rst_if.wait_for_reset();
          `uvm_info(`gfn, $sformatf("CPU reset cycled."), UVM_LOW)
        end
      join
      ,
      // Exit thread: allow at most 20 AON clock cycles until the above domains must reset.
      cfg.chip_vif.aon_clk_por_rst_if.wait_clks(20);
      `dv_error("Resets did not complete within required time!")
    )

    // Deactivate external reset request.
    cfg.chip_vif.signal_probe_soc_rst_req_async(.kind(dv_utils_pkg::SignalProbeRelease));

    // Wait until SW confirms reset on external request.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Reset on external request.")
  endtask

endclass
