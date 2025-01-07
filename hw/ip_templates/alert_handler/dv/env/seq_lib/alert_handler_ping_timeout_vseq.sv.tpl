// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence test corner cases for alert or escalation pings:
// 1). ping integrity fail or timeout
// 2). ping interrupted by a reset signal
// 3). escalation ping interrupted by real escalation signal (this could happen because escalation
//     ping and real escalation share the same esc_p/n signals)

class alert_handler_ping_timeout_vseq extends alert_handler_entropy_vseq;
  `uvm_object_utils(alert_handler_ping_timeout_vseq)

  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[5:30]};
  }

  constraint alert_trigger_c {
    alert_trigger == 0;
  }

  constraint intr_en_c {
    intr_en == '1;
  }

  constraint sig_int_c {
    alert_int_err          == 0;
    esc_int_err            == 0;
    esc_standalone_int_err == 0;
  }

  constraint loc_alert_en_c {
    local_alert_en[LocalEscPingFail] == 1;
    local_alert_en[LocalAlertPingFail] == 1;
  }

  constraint ping_fail_c {
    alert_ping_timeout == '1;
    esc_ping_timeout   == '1;
  }

  // At least enable and lock `NUM_ALERTS-4` alerts to avoid this sequence running too long.
  // This constraint also ensures at least one alert is locked and enabled so that we can ensure at
  // least one alert ping will fire.
  constraint enable_one_alert_c {
    $countones(alert_en)      dist {NUM_ALERTS :/ 8, [NUM_ALERTS-4 : NUM_ALERTS-1] :/ 2};
    $countones(~alert_regwen) dist {NUM_ALERTS :/ 5, [NUM_ALERTS-4 : NUM_ALERTS-1] :/ 5};
    (~alert_regwen) & alert_en > 0;
  }

  constraint ping_timeout_cyc_c {
    ping_timeout_cyc inside {[1:MAX_PING_TIMEOUT_CYCLE]};
  }

  // disable interrupt timeout
  constraint esc_intr_timeout_c {
    foreach (intr_timeout_cyc[i]) {intr_timeout_cyc[i] == 0;}
  }

  function void pre_randomize();
    this.enable_classa_only_c.constraint_mode(0);
  endfunction

  // In this sequence, because we disable all external alerts, so to ensure local alerts are
  // triggerd, we wait for interrupt pins to fire then wait for alert and escalation handshake
  // to finish.
  virtual task wait_alert_esc_done();
    wait (cfg.intr_vif.pins[NUM_ALERT_CLASSES-1:0]);
    // Wait two clock cycles to avoid building a cycle-accurate scb.
    cfg.clk_rst_vif.wait_clks(2);
    `uvm_info(`gfn, $sformatf("Interrupt pin = %0h", cfg.intr_vif.pins[NUM_ALERT_CLASSES-1:0]),
              UVM_LOW)
    check_alert_interrupts();
    super.wait_alert_esc_done();
  endtask

endclass : alert_handler_ping_timeout_vseq
