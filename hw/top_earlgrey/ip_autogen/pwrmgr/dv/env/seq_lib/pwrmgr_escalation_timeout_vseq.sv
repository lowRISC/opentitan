// Copyright lowRISC contributors.
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
        cfg.esc_clk_rst_vif.start_clk();
        cfg.esc_clk_rst_vif.wait_clks(10000);
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
    wait_for_fast_fsm_active();
    cfg.slow_clk_rst_vif.set_freq_mhz(1);
    cfg.esc_clk_rst_vif.wait_clks(200);
    check_stopped_esc_clk(120, 1'b0);
    check_stopped_esc_clk(2000, 1'b1);
    wait_for_fast_fsm_active();
    // This fails to generate a reset, so the test fails. It should pass once
    // lowrisc/opentitan#20516 is addressed.
    check_stopped_esc_clk(136, 1'b1);
  endtask : body

endclass
