// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sysrst_ctrl_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_vseq)

  `uvm_object_new

  // two key rsts + one pad rst
  parameter int NumPadRstEvent = 3;
  // one sw por + one sw_req
  parameter int NumWdogRstEvent = 2;
  parameter int NumRound = NumPadRstEvent + NumWdogRstEvent;

  rand int cycles_after_trigger;
  rand int cycles_till_reset;
  rand bit reset_delay;
  int loop_num;

  constraint cycles_after_trigger_c {cycles_after_trigger inside {[0 : 9]};}
  constraint cycles_tll_reset_c {cycles_till_reset inside {[0 : 200]};}

  rand bit[7:0] assa[NumRound-1];
  constraint assa_c {
    foreach (assa[i]) assa[i] inside {[0:3]};
  }

  virtual task cpu_init();
    bit[7:0] rst_idx[NumRound];
    loop_num = 0;

    for (int i=0; i<NumRound; i=i+1) begin
      if (i==4) begin
        rst_idx[i] = i;
      end
      else begin
        rst_idx[i] = assa[i];
        if (rst_idx[i]!=2) begin
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
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `uvm_info(`gfn, "SW test ready", UVM_MEDIUM)

    repeat (loop_num) begin
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "Reset Request SourceOne is set" |
            cfg.sw_logger_vif.printed_log == "Booting and setting deep sleep followed by hw por" |
            cfg.sw_logger_vif.printed_log == "Last Booting" |
            cfg.sw_logger_vif.printed_log == "Test finish")

       if (cfg.sw_logger_vif.printed_log == "Reset Request SourceOne is set") begin
         `uvm_info(`gfn, "SW message delivered to TB", UVM_MEDIUM)
         repeat (10) @cfg.chip_vif.pwrmgr_low_power_if.cb;  //
         repeat (cycles_till_reset) @cfg.chip_vif.pwrmgr_low_power_if.cb;
         `uvm_info(`gfn, $sformatf("sysrst req set after fixed delay : %d + variable delay : %d",
                 10, cycles_till_reset), UVM_MEDIUM)
         cfg.ast_supply_vif.pulse_key0_i_next_trigger(50 + cycles_after_trigger);
       end
       else if (cfg.sw_logger_vif.printed_log ==
                 "Booting and setting deep sleep followed by hw por") begin
         repeat (10) @cfg.chip_vif.pwrmgr_low_power_if.cb;
         repeat (cycles_till_reset) @cfg.chip_vif.pwrmgr_low_power_if.cb;
         `uvm_info(`gfn, $sformatf("sysrst req set after fixed delay : %d + variable delay : %d",
                 10, cycles_till_reset), UVM_MEDIUM)
         execute_reset();
       end
    end
  endtask

  task execute_reset();
    `uvm_info(`gfn, "wait for low power entry", UVM_MEDIUM)
    `DV_WAIT(cfg.chip_vif.pwrmgr_low_power_if.low_power == 1)
    `uvm_info(`gfn, "reset after low power entry", UVM_MEDIUM)
    assert_por_reset(reset_delay);
  endtask // execute_reset

endclass
