// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This requesnt randomly assert reset or wakeup 10 times
// each time sequence waits for 'ready for power down' log from c test
// then execute reset / wakeup or both.
// After that it waits for dut reboot before it goes to the next round
class chip_sw_repeat_reset_wkup_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_repeat_reset_wkup_vseq)
  typedef enum {TEST_WKUP, TEST_RST, TEST_BOTH} wk_or_rst_e;

  `uvm_object_new
  int num_round = 10;

  rand wk_or_rst_e input_type;
  rand bit add_cycle;
   rand bit reset_delay;

  virtual task cpu_init();
    bit[7:0] byte_arr[1] = {num_round};
    super.cpu_init();
    sw_symbol_backdoor_overwrite("kNumRound", byte_arr);
  endtask

  virtual task pre_start();
    super.pre_start();
    cfg.chip_vif.pwrb_in_if.drive(1);
  endtask

  virtual task body();
    super.body();

    for (int i = 0; i < num_round; ++i) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)

      // Wait until we reach the SW test state.
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "ready for power down")

      `uvm_info(`gfn, $sformatf("round %0d input_type: %s add_cycle: %d  reset_dealy: %d ",
                                i, input_type.name(), add_cycle, reset_delay), UVM_MEDIUM)

      if (input_type == TEST_WKUP) begin
        // wakup is sync with slow clock.
        // We can't align edge with fsm state (main_clk)
        execute_wakeup();
      end else if (input_type == TEST_RST) begin
        // POR move fsm to FastPwrStateLowPower right away
        // We always align with edge with low power state
        execute_reset();
      end else begin
        fork
          execute_wakeup();
          execute_reset();
        join
      end

      // after reset / wakep, waitfor reboot
      // before test goes to the next round
      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    end
  endtask // body

  task execute_wakeup();
    #30us;
    if (add_cycle == 1) begin
      `uvm_info(`gfn, "wake up after low power entry", UVM_MEDIUM)
      repeat((1 + reset_delay))@cfg.chip_vif.pwrmgr_low_power_if.cb;
    end
    push_button();
  endtask // execute_wakeup

  task execute_reset();
    if (add_cycle == 1) begin
      `uvm_info(`gfn, "reset after low power entry", UVM_MEDIUM)
      `DV_WAIT(cfg.chip_vif.pwrmgr_low_power_if.low_power == 1)

    end
    assert_por_reset(reset_delay);
  endtask // execute_reset
endclass
