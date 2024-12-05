// Copyright lowRISC contributors (OpenTitan project).
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

  // disable interrupt timeout
  constraint esc_intr_timeout_c {
    foreach (intr_timeout_cyc[i]) {intr_timeout_cyc[i] == 0;}
  }

  function void pre_randomize();
    this.enable_classa_only_c.constraint_mode(0);
    this.enable_one_alert_c.constraint_mode(0);
    verbosity = UVM_HIGH;
  endfunction

  task body();
    fork
      begin : isolation_fork
        trigger_non_blocking_seqs();
        fork
          enable_lpg_group(alert_en);
          run_smoke_seq();
        join
        disable fork; // disable non-blocking seqs for stress_all tests
      end // end isolation_fork
    join
  endtask : body
endclass : alert_handler_lpg_vseq
