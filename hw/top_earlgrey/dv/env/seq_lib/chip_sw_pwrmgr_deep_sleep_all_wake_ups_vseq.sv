// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cfg.chip_vif.pwrb_in_if.drive(1'b1);    // off
  endtask

  virtual task body();
    uint                timeout_long = 10_000_000;
    uint                timeout_short = 1_000_000;
    super.body();

    // Need to use hard coded string.
    // Loop with sformatf %d doesn't work
     // Add sample number for the future reference.
     // This is sampled from sv simulation and can be varied
     // over test run as well as the version of design.
     // Total run time was 21ms.
     // @3.5ms
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 0");,
                   "Timed out waiting for enter sleep 0", timeout_long)
      wakeup_action(0);
     // @6.3ms
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Woke up by source 0");,
                   "Timed out waiting for Woke up by source 0", timeout_long)
      release_action(0);
     // @6.45ms
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 1");,
                   "Timed out waiting for enter sleep 1", timeout_short)
      wakeup_action(1);
     // @12.28ms
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Woke up by source 1");,
                   "Timed out waiting for Woke up by source 1", timeout_long)
      release_action(1);
     // @12.425
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 2");,
                   "Timed out waiting for enter sleep 2", timeout_short)
      wakeup_action(2);
     // @15.248
      `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Woke up by source 2");,
                   "Timed out waiting for Woke up by source 2", timeout_long)
      release_action(2);
 endtask // body

  // Trigger wakeup signal for each test round
  // Round 0 : input for sysrst ctrl
  // Round 1 : input for adc ctrl (force)
  // Round 2 : input for pinmux wakeup detector
  task wakeup_action(int round);
    string path1 ,path2;
     repeat(20) @(posedge cfg.ast_supply_vif.clk);
    case(round)
      0: begin
        `uvm_info(`gfn, "Push power button ", UVM_MEDIUM)
        cfg.chip_vif.pwrb_in_if.drive(1'b0); // on
      end
      1: begin
        `uvm_info(`gfn, "Force adc out ", UVM_MEDIUM)
        // Force to random positive value
        path1 = "tb.dut.u_ast.u_adc.u_adc_ana.adc_d_ch0_o";
        path2 = "tb.dut.u_ast.u_adc.u_adc_ana.adc_d_ch1_o";
        `DV_CHECK(uvm_hdl_force(path1, 5))
        `DV_CHECK(uvm_hdl_force(path2, 115))
      end
      2: begin
        `uvm_info(`gfn, "Send pattern to pinmux wakeup detector ", UVM_MEDIUM)
        cfg.chip_vif.pinmux_wkup_if.drive(1'b1);
      end
      default: `uvm_fatal(`gfn, $sformatf("round %d is not allowed", round))
    endcase
  endtask // wakeup_action

  // Release wakeup signals
  task release_action(int round);
    string path1 ,path2;
    case(round)
      0: cfg.chip_vif.pwrb_in_if.drive(1'b1);
      1: begin
        path1 = "tb.dut.u_ast.u_adc.u_adc_ana.adc_d_ch0_o";
        path2 = "tb.dut.u_ast.u_adc.u_adc_ana.adc_d_ch1_o";
        `DV_CHECK(uvm_hdl_release(path1))
        `DV_CHECK(uvm_hdl_release(path2))
      end
      2:     cfg.chip_vif.pinmux_wkup_if.drive(1'b0);
      default: `uvm_fatal(`gfn, $sformatf("round %d is not allowed", round))
    endcase
  endtask // release_action
endclass // chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq
