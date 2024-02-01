// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// This test checks that an escalation reset is generated when the escalation clock stops for
// enough cycles.
class pwrmgr_escalation_timeout_vseq extends pwrmgr_base_vseq;
  `uvm_object_utils(pwrmgr_escalation_timeout_vseq)

  `uvm_object_new

  localparam int TIMEOUT_THRESHOLD = 128;

  int trans_cnt = 0;
  constraint num_trans_c {num_trans inside {[1 : 5]};}

  task check_stopped_esc_clk(int stop_cycles, bit expect_reset);
    fork
      begin
        `uvm_info(`gfn, $sformatf("Stopping escalation clock for %0d cycles", stop_cycles),
                  UVM_MEDIUM)
        cfg.esc_clk_rst_vif.stop_clk();
        cfg.clk_rst_vif.wait_clks(stop_cycles);
        `uvm_info(`gfn, "Restarting escalation clock", UVM_MEDIUM)
        cfg.esc_clk_rst_vif.start_clk();
        cfg.esc_clk_rst_vif.wait_clks(4000);
      end
      begin
        cfg.clk_rst_vif.wait_clks(TIMEOUT_THRESHOLD);
        if (expect_reset) begin
          `DV_WAIT(cfg.pwrmgr_vif.fetch_en != lc_ctrl_pkg::On,
                   "Timeout waiting for cpu fetch disable", 4000)
          `uvm_info(`gfn, "cpu fetch disabled, indicating a reset", UVM_MEDIUM)
          `DV_WAIT(cfg.pwrmgr_vif.pwr_rst_req.rstreqs[pwrmgr_reg_pkg::ResetEscIdx] == 1'b1 &&
                   cfg.pwrmgr_vif.pwr_rst_req.reset_cause == pwrmgr_pkg::HwReq,
                   "Timeout waiting for outgoing escalation reset", 40000)
          `uvm_info(`gfn, "Outgoing escalation reset", UVM_MEDIUM)
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
    // The timeout is not predictable for two reasons:
    // - The initial count for the timeout can be from 0 to 7, which means the timeout could
    //   happen between 121 and 128 cycles after the clock.
    // - The timeout has a req-ack synchronizer which has some randomness due to the phase.
    //   This adds a few more cycles of uncertainty.
    // Keep the clock stopped for less than 118 cycles should be safe to avoid an alert.
    check_stopped_esc_clk(118, 1'b0);
    check_stopped_esc_clk(2000, 1'b1);
    wait_for_fast_fsm(FastFsmActive);
    // This should generate a reset but it doesn't so the test will fail.
    // TODO(lowrisc/opentitan#20516): Enable this test when this is fixed.
    // check_stopped_esc_clk(136, 1'b1);
  endtask : body

endclass
