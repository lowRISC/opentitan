// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_deep_sleep_all_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_deep_sleep_all_reset_vseq)

  `uvm_object_new

  // Possible resets: sysrst, watchdog, rstmgr sw reset, escalation reset.

  rand int cycles_after_trigger;
  rand int cycles_till_reset;
  rand int reset_delay;

  constraint cycles_after_trigger_c {cycles_after_trigger inside {[0 : 9]};}
  constraint cycles_tll_reset_c {cycles_till_reset inside {[0 : 200]};}
  constraint reset_delay_c {reset_delay inside {[0 : 10]};}

  virtual task body();
    int loop_idx = 0;
    super.body();
    // mimic external pull up in key in0
    cfg.ast_supply_vif.force_key0_i(1'b1);
    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest,
             "Timed out waitingfor SwTestSTatusInTest",
             40_000_000)
    `uvm_info(`gfn, "SW test ready", UVM_MEDIUM)

    while (1) begin
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "New reset event")
      `DV_WAIT(
            cfg.sw_logger_vif.printed_log == "Sysrst reset in active mode" ||
            cfg.sw_logger_vif.printed_log == "Sysrst reset in deep sleep mode" ||
            cfg.sw_logger_vif.printed_log == "Sysrst reset in normal sleep mode" ||
            cfg.sw_logger_vif.printed_log == "Let SV wait timer reset" ||
            cfg.sw_logger_vif.printed_log == "Last Booting" ||
            cfg.sw_logger_vif.printed_log == "Test finish")

      `uvm_info(`gfn, $sformatf("SW message delivered to TB\n >> %0s",
                                cfg.sw_logger_vif.printed_log), UVM_MEDIUM)
      if (cfg.sw_logger_vif.printed_log == "Sysrst reset in active mode" ||
          cfg.sw_logger_vif.printed_log == "Sysrst reset in deep sleep mode" ||
          cfg.sw_logger_vif.printed_log == "Sysrst reset in normal sleep mode") begin
        repeat (10) @cfg.chip_vif.pwrmgr_low_power_if.cb;
        repeat (cycles_till_reset) @cfg.chip_vif.pwrmgr_low_power_if.cb;
        `uvm_info(`gfn, $sformatf("sysrst req set after fixed delay : %0d + variable delay : %0d",
                                  10, cycles_till_reset), UVM_MEDIUM)
        cfg.ast_supply_vif.pulse_key0_i_next_trigger(50 + cycles_after_trigger);
      end else if (cfg.sw_logger_vif.printed_log == "Let SV wait timer reset") begin
        // Wait until c test finishes the current round and goes to reset.
        `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
      end else begin
        // Add some time slap for dummy wait event
        repeat (10) @cfg.chip_vif.pwrmgr_low_power_if.fast_cb;
      end

      // Wait for reboot except the last round
      if (cfg.sw_logger_vif.printed_log == "Last Booting" ||
          cfg.sw_logger_vif.printed_log == "Test finish") begin
        break;
      end
      `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
    end
  endtask

endclass
