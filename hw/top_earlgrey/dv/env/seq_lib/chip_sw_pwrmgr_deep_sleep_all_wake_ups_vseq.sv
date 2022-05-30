// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    cfg.pwrb_in_vif.drive(1'b1);    // off
  endtask

  virtual task body();
    super.body();

    // Need to use hard coded string.
    // Loop with sformatf %d doesn't work
      wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 0");
      wakeup_action(0);
      wait(cfg.sw_logger_vif.printed_log == "Woke up by source 0");
      release_action(0);
      wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 1");
      wakeup_action(1);
      wait(cfg.sw_logger_vif.printed_log == "Woke up by source 1");
      release_action(1);
      wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sleep 2");
      wakeup_action(2);
      wait(cfg.sw_logger_vif.printed_log == "Woke up by source 2");
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
        cfg.pwrb_in_vif.drive(1'b0); // on
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
        cfg.pinmux_wkup_vif.drive(1'b1);
      end
      default: `uvm_fatal(`gfn, $sformatf("round %d is not allowed", round))
    endcase
  endtask // wakeup_action

  // Release wakeup signals
  task release_action(int round);
    string path1 ,path2;
    case(round)
      0: cfg.pwrb_in_vif.drive(1'b1);
      1: begin
        path1 = "tb.dut.u_ast.u_adc.u_adc_ana.adc_d_ch0_o";
        path2 = "tb.dut.u_ast.u_adc.u_adc_ana.adc_d_ch1_o";
        `DV_CHECK(uvm_hdl_release(path1))
        `DV_CHECK(uvm_hdl_release(path2))
      end
      2:     cfg.pinmux_wkup_vif.drive(1'b0);
      default: `uvm_fatal(`gfn, $sformatf("round %d is not allowed", round))
    endcase
  endtask // release_action
endclass // chip_sw_pwrmgr_deep_sleep_all_wake_ups_vseq
