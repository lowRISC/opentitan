// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_random_sleep_all_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_random_sleep_all_reset_vseq)

  `uvm_object_new

  // NumRound = 12 is the number of resets in this test. It consists of one PoR
  // reset (1st one) + 11 random reset. 11 random resets are 10 sleep mode
  // (light sleep and deep sleep) and one normal mode. The reset array rst_idx has
  // 12 (NumRound) reset elements where 11 (NumRound-1) random reset sequence is
  // ordered using a random variable assa. The last reset does not have to set the next reset type.

  parameter int NumSleepType = 2;
  // (key rst + pad rst) x 2 (normal sleep/deep sleep)
  parameter int NumPadRstEvent = 2 * NumSleepType;
  // (sw_req + escalation rst + normal watchdog) x 2
  parameter int NumWdogRstEvent = 3 * NumSleepType;
  parameter int NumNormalMode = 1;
  parameter int NumRound = NumPadRstEvent + NumWdogRstEvent + NumNormalMode + 1;

  rand int cycles_after_trigger;
  rand int cycles_till_reset;
  rand bit reset_delay;
  int loop_num;

  constraint cycles_after_trigger_c {cycles_after_trigger inside {[0 : 9]};}
  constraint cycles_tll_reset_c {cycles_till_reset inside {[0 : 200]};}
  constraint reset_delay_c {reset_delay inside {[0 : 10]};}

  rand bit[7:0] assa[NumRound-1];
  constraint assa_c {
    foreach (assa[i]) assa[i] inside {[0:NumRound-2]};
  }

  virtual task cpu_init();
    bit[7:0] rst_idx[NumRound];
    loop_num = 0;
    for (int i=0; i< NumRound; i = i+1) begin
      if (i == (NumRound-1)) begin
        rst_idx[i] = i;
      end
      else begin
        rst_idx[i] = assa[i];
        if (rst_idx[i] inside {[0:3]}) begin
          loop_num = loop_num + 1;
        end
      end
    end

    `uvm_info(`gfn, $sformatf("HW rst loop # : %d", loop_num), UVM_MEDIUM)

    super.cpu_init();
    sw_symbol_backdoor_overwrite("RST_IDX", rst_idx);
  endtask

  virtual task body();
    super.body();
    // mimic external pull up in key in0
    cfg.ast_supply_vif.force_key0_i(1'b1);
    // Wait until we reach the SW test state.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
    `uvm_info(`gfn, "SW test ready", UVM_MEDIUM)

    repeat (loop_num) begin
      wait (cfg.sw_logger_vif.printed_log == "Booting and setting deep sleep followed by hw por" ||
            cfg.sw_logger_vif.printed_log ==
                "Booting and setting normal sleep followed by hw por" ||
            cfg.sw_logger_vif.printed_log == "Booting and setting deep sleep followed by sysrst" ||
            cfg.sw_logger_vif.printed_log ==
                "Booting and setting normal sleep followed by sysrst" ||
            cfg.sw_logger_vif.printed_log == "Last Booting" ||
            cfg.sw_logger_vif.printed_log == "Test finish");

       if (cfg.sw_logger_vif.printed_log == "Booting and setting deep sleep followed by sysrst" ||
           cfg.sw_logger_vif.printed_log == "Booting and setting normal sleep followed by sysrst")
           begin
         `uvm_info(`gfn, "SW message delivered to TB", UVM_MEDIUM)
         repeat (10) @cfg.pwrmgr_low_power_vif.cb;  //
         repeat (cycles_till_reset) @cfg.pwrmgr_low_power_vif.cb;
         `uvm_info(`gfn, $sformatf("sysrst req set after fixed delay : %d + variable delay : %d",
                                    10, cycles_till_reset), UVM_MEDIUM)
         cfg.ast_supply_vif.pulse_key0_i_next_trigger(50 + cycles_after_trigger);
       end
       else if (cfg.sw_logger_vif.printed_log ==
                "Booting and setting deep sleep followed by hw por" |
                cfg.sw_logger_vif.printed_log ==
                "Booting and setting normal sleep followed by hw por") begin
         `uvm_info(`gfn, "SW message delivered to TB", UVM_MEDIUM)
         repeat (10) @cfg.pwrmgr_low_power_vif.cb;
         repeat (cycles_till_reset) @cfg.pwrmgr_low_power_vif.cb;
         `uvm_info(`gfn, $sformatf("sysrst req set after fixed delay : %d + variable delay : %d",
                                    10, cycles_till_reset), UVM_MEDIUM)
         execute_reset();
       end
    end
  endtask

  virtual task pre_start();
    super.pre_start();
  endtask

  task execute_reset();
    `uvm_info(`gfn, "wait for low power entry", UVM_MEDIUM)
    wait(cfg.pwrmgr_low_power_vif.low_power == 1);
    `uvm_info(`gfn, "reset after low power entry", UVM_MEDIUM)
    assert_por_reset_deep_sleep (reset_delay);
  endtask // execute_reset

endclass
