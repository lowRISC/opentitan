// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test builds on the existing host_perf test, but utilizes an additional monitor mode to
// measure the bit-period of each data bit throughout a transfer. ACK-bits are excluded by
// controlling the sampling point inside the monitor.
// See i2c_monitor::perf_monitor() for implementation details.
//
class i2c_host_perf_precise_vseq extends i2c_host_perf_vseq;
  `uvm_object_utils(i2c_host_perf_precise_vseq)
  `uvm_object_new

  // Limit the number of runs to shorten the length of the test a bit
  // (the host_perf_vseq parent class with 5 runs takes 48m in total!)
  constraint num_trans_c {num_trans == 1;}

  // Override the parent class's implementation to make a more precise measurement
  // of the bus performance.
  virtual task perf_monitor();
    fork
      begin
        string str = "";
        // Watch for the performance monitor process to complete, then check the values it
        // has captured.
        cfg.m_i2c_agent_cfg.stop_perf_monitor.wait_trigger();

        `uvm_info(`gfn, $sformatf("clk_period_ps=%0d ps", cfg.clk_rst_vif.clk_period_ps), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("coerced_scl_period=%0d cycles", coerced_scl_period), UVM_HIGH)

        // LOG
        str = {str, "i2c_host_perf_precise_vseq saw the following SCL periods:"};
        foreach (cfg.m_i2c_agent_cfg.period_q[i]) begin
          str = {str, $sformatf("\n[%0d] %t", i, cfg.m_i2c_agent_cfg.period_q[i])};
        end
        `uvm_info(`gfn, str, UVM_MEDIUM)

        // CHECK
        foreach (cfg.m_i2c_agent_cfg.period_q[i]) begin
          // We captured the period using $realtime. Convert it back to cycles for comparison
          uint obs_scl_period = uint'(real'(cfg.m_i2c_agent_cfg.period_q[i]) /
                                      real'(cfg.clk_rst_vif.clk_period_ps * 1ps));
          `uvm_info(`gfn, $sformatf("obs_scl_period[%0d]=%0d cycles", i, obs_scl_period), UVM_DEBUG)

          if (obs_scl_period != coerced_scl_period) begin
            `uvm_error(`gfn,
                       $sformatf({"Observed SCL period[%0d] (%0d cycles) did not match expected!",
                                  " (%0d cycles)"}, i, obs_scl_period, coerced_scl_period))
          end
        end
      end
    join_none
  endtask

  virtual task post_start(); endtask

endclass : i2c_host_perf_precise_vseq
