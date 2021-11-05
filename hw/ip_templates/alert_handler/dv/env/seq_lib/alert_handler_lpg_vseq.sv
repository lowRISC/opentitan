// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_lpg_vseq extends alert_handler_entropy_vseq;
  `uvm_object_utils(alert_handler_lpg_vseq)

  `uvm_object_new

  constraint sig_int_c {
    alert_int_err          == 0;
    esc_int_err            == 0;
    esc_standalone_int_err == 0;
  }

  constraint loc_alert_en_c {
    local_alert_en[LocalAlertPingFail] > 0;
  }

  constraint ping_fail_c {
    alert_ping_timeout == alert_en;
    esc_ping_timeout   == 0;
  }

  constraint alert_trigger_c {
    alert_trigger == 0;
  }

  // disable interrupt timeout
  constraint esc_intr_timeout_c {
    foreach (intr_timeout_cyc[i]) {intr_timeout_cyc[i] == 0;}
  }

  function void pre_randomize();
    this.enable_classa_only_c.constraint_mode(0);
    this.enable_one_alert_c.constraint_mode(0);
    verbosity = UVM_HIGH;
  endfunction

  function void disable_lpg_group(bit [NUM_ALERTS-1:0] alert_en_i);
    foreach (alert_en_i[i]) begin
      int index = alert_handler_reg_pkg::LpgMap[i];
      if ($urandom_range(0, 1)) cfg.alert_handler_vif.set_lpg_cg_en(index);
      if ($urandom_range(0, 1)) cfg.alert_handler_vif.set_lpg_rst_en(index);
    end
  endfunction

  task body();
    fork
      begin : isolation_fork
        trigger_non_blocking_seqs();
        disable_lpg_group(alert_en);
        run_smoke_seq();
        disable fork; // disable non-blocking seqs for stress_all tests
      end // end fork
    join
  endtask : body
endclass : alert_handler_lpg_vseq
