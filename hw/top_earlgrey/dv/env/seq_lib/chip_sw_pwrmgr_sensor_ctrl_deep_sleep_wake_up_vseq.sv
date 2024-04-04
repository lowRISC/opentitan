// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_pwrmgr_sensor_ctrl_deep_sleep_wake_up_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_pwrmgr_sensor_ctrl_deep_sleep_wake_up_vseq)
  `uvm_object_new


  virtual task body();
    uint timeout_long  = 10_000_000;
    uint timeout_short = 1_000_000;

    super.body();

    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Issue WFI to enter sensor_ctrl sleep");,
                   "Timed out waiting for enter sensor_ctrl sleep", timeout_long)
    #400us;
    cfg.chip_vif.trigger_sensor_ctrl_wkup();
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Woke up by sensor_ctrl");,
                   "Timed out waiting for wake up sensor_ctrl sleep", timeout_long)

  endtask

endclass : chip_sw_pwrmgr_sensor_ctrl_deep_sleep_wake_up_vseq
