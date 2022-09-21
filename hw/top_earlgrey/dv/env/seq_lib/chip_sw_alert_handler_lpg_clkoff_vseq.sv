// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_alert_handler_lpg_clkoff_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_alert_handler_lpg_clkoff_vseq)

  `uvm_object_new

  virtual task pre_start();
    void'(cfg.chip_vif.signal_probe_alert_handler_ping_timer_wait_cyc_mask_i(SignalProbeForce, 7));
    super.pre_start();
  endtask

endclass
