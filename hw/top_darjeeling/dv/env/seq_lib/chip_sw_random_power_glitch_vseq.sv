// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_random_power_glitch_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_random_power_glitch_vseq)

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
  rand int reset_delay;

  constraint cycles_after_trigger_c {cycles_after_trigger inside {[300 : 320]};}
  constraint cycles_tll_reset_c {cycles_till_reset inside {[0 : 200]};}
  constraint reset_delay_c {reset_delay inside {[0 : 4]};}

  rand bit[7:0] assa[NumRound-1];
  constraint assa_c {
    foreach (assa[i]) assa[i] inside {[0:NumRound-2]};
  }

  virtual task cpu_init();
    bit[7:0] rst_idx[NumRound];
    for (int i=0; i< NumRound; i = i+1) begin
      if (i == (NumRound-1)) begin
        rst_idx[i] = i;
      end
      else begin
        rst_idx[i] = assa[i];
      end
    end

    super.cpu_init();
    sw_symbol_backdoor_overwrite("RST_IDX", rst_idx);
  endtask

  virtual task body();
    super.body();
    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `uvm_info(`gfn, "SW test ready", UVM_MEDIUM)
    repeat (NumRound) begin
      // The timeout for this test needs to be larger than 30_000_000, otherwise certain seeds
      // like:
      // ./util/dvsim/dvsim.py hw/top_earlgrey/dv/chip_sim_cfg.hjson -i \
      //   chip_sw_pwrmgr_random_sleep_power_glitch_reset --build-seed 4232114340 \
      //   --fixed-seed 2369106033 --verbosity m
      // will fail.
      `DV_WAIT(
            cfg.sw_logger_vif.printed_log ==
                "Booting and setting deep sleep followed by hw por" ||
            cfg.sw_logger_vif.printed_log ==
                "Booting and setting normal sleep followed by hw por" ||
            cfg.sw_logger_vif.printed_log ==
                "Booting and setting deep sleep followed by glitch reset" ||
            cfg.sw_logger_vif.printed_log ==
                "Booting and setting normal sleep followed by glitch reset" ||
            cfg.sw_logger_vif.printed_log == "Last Booting" ||
            cfg.sw_logger_vif.printed_log == "Test finish", , 40_000_000
            )

       `uvm_info(`gfn, "HW Booting is called", UVM_MEDIUM)
       if (cfg.sw_logger_vif.printed_log ==
                "Booting and setting deep sleep followed by glitch reset" ||
           cfg.sw_logger_vif.printed_log ==
                "Booting and setting normal sleep followed by glitch reset")
           begin
         `uvm_info(`gfn, "SW message delivered to TB", UVM_MEDIUM)
         if (cfg.sw_logger_vif.printed_log ==
                "Booting and setting deep sleep followed by glitch reset") begin
           `uvm_info(`gfn, "glitch for deep sleep", UVM_MEDIUM)
           cfg.ast_supply_vif.glitch_vcmain_pok_on_next_low_power_trigger();
         end
         else begin
           `uvm_info(`gfn, "glitch for normal sleep", UVM_MEDIUM)
           cfg.ast_supply_vif.glitch_vcmain_pok_on_next_core_sleeping_trigger(cycles_after_trigger);
         end
       end
       else if (cfg.sw_logger_vif.printed_log ==
                "Booting and setting deep sleep followed by hw por" |
                cfg.sw_logger_vif.printed_log ==
                "Booting and setting normal sleep followed by hw por") begin
         `uvm_info(`gfn, "SW message delivered to TB", UVM_MEDIUM)
         repeat (10 + cycles_till_reset) @cfg.chip_vif.pwrmgr_low_power_if.cb;
         `uvm_info(`gfn, $sformatf("POR reset req set after fixed delay : %d + variable delay : %d",
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
    `DV_WAIT(cfg.chip_vif.pwrmgr_low_power_if.low_power == 1)
    `uvm_info(`gfn, "reset after low power entry", UVM_MEDIUM)
    assert_por_reset_deep_sleep (reset_delay);
  endtask // execute_reset

endclass
