// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Description:
// This test checks that an escalation reset is generated when the escalation clock stops for
// enough cycles.
class pwrmgr_escalation_timeout_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_escalation_timeout_vseq)

  `uvm_object_new

  // The following two parameters are used to determine when to perform checks.

  // The number of clock cycles with a stopped escalation clock before raising escalation is 128.
  // But the logic can wait for up to 7 more cycles before it starts the counter, and there is
  // some additional fast clock cycles of delay in the logic that triggers the escalation to
  // be signalled. This adds 12 extra cycles to be conservative.
  localparam int EscTimeoutMainClkThreshold = 128 + 7 + 12;

  // In addition, there is a clock domain crossing to the slow clock, which can add a couple slow
  // clocks cycles plus an extra cycle for the input to meet the next clock cycle.
  localparam int EscTimeoutSlowClkThreshold = 2 + 1;

  int trans_cnt = 0;
  constraint num_trans_c {num_trans inside {[1 : 5]};}

  // This stops the escalation clock for a certain number of cycles, and
  // checks a reset occurs or not, depending on expect_reset.
  task check_stopped_esc_clk(int stop_cycles, bit expect_reset);
    fork
      begin
        `uvm_info(`gfn, $sformatf(
                  "Stopping escalation clock for %0d cycles %s expecting reset",
                  stop_cycles, expect_reset ? "" : "not "),
                  UVM_MEDIUM)
        cfg.esc_clk_rst_vif.stop_clk();
        // The clock will be restarted while handling a reset, so no need to restart it here.
        if (!expect_reset) begin
          cfg.clk_rst_vif.wait_clks(stop_cycles);
          `uvm_info(`gfn, "Restarting escalation clock", UVM_MEDIUM)
          cfg.esc_clk_rst_vif.start_clk();
          cfg.esc_clk_rst_vif.wait_clks(4000);
        end
      end
      begin
        if (expect_reset) begin
          // The expectation is to create an outgoing reset request, disable cpu fetching, and the
          // reset cause to indicate a hardware request.
          // Turn the cycle counts into a number of nanoseconds for waiting with timeout.
          // The clk_rst_vifs give the period in pico seconds so divide by 1000.
          int wait_ns = (EscTimeoutMainClkThreshold * cfg.clk_rst_vif.clk_period_ps +
                         EscTimeoutSlowClkThreshold * cfg.slow_clk_rst_vif.clk_period_ps) / 1000;
          `DV_SPINWAIT(
            wait(cfg.pwrmgr_vif.fetch_en != lc_ctrl_pkg::On &&
                 cfg.pwrmgr_vif.pwr_rst_req.rstreqs[pwrmgr_reg_pkg::ResetEscIdx] == 1'b1 &&
                 cfg.pwrmgr_vif.pwr_rst_req.reset_cause == pwrmgr_pkg::HwReq);
            `uvm_info(`gfn, "escalation reset completed", UVM_LOW),
            "escalation reset was not completed as expected", wait_ns)
        end else begin
          repeat (8000) begin
            cfg.clk_rst_vif.wait_clks(1);
            if (cfg.pwrmgr_vif.fetch_en != lc_ctrl_pkg::On) begin
              `uvm_error(`gfn, "Unexpected cpu fetch disable, indicating a reset")
            end
          end
        end
      end
    join
  endtask

  virtual task body();
    wait_for_fast_fsm(FastFsmActive);
    cfg.slow_clk_rst_vif.set_freq_mhz(1);
    cfg.esc_clk_rst_vif.wait_clks(200);
    // The timeout is not accurately predictable for two reasons:
    // - The initial count for the timeout can be from 0 to 7, which means the timeout could
    //   happen between 121 and 128 cycles after the clock.
    // - The timeout has a req-ack synchronizer which has some randomness due to the phase.
    //   This adds a few more cycles of uncertainty.
    // Keep the clock stopped for less than 118 cycles should be safe to avoid an alert.
    check_stopped_esc_clk(118, 1'b0);
    check_stopped_esc_clk(2000, 1'b1);
    wait_for_fast_fsm(FastFsmActive);
    check_stopped_esc_clk(136, 1'b1);
  endtask : body

endclass
