// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// disable alert ping check at catastrophic event test.
class chip_sw_rstmgr_alert_info_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_rstmgr_alert_info_vseq)
  `uvm_object_new

  virtual task body();
    super.body();
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Disable ping timer alert check");,
                "timeout waiting for C side synchronization",
                cfg.sw_test_timeout_ns)
    cfg.en_scb_ping_chk = 0;
  endtask
endclass
