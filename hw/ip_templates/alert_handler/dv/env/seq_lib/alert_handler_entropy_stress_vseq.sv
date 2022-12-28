// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence uses a fixed setting to enable all alerts and locks them to class A.
// Then enable all local alerts and locks them to class B.
// Randomly force the `wait_cyc_mask_i` from design to a valid small number to fasten the ping
// request mechanism.
// Finally this sequence wait until alerts are pinged certain times.
class alert_handler_entropy_stress_vseq extends alert_handler_smoke_vseq;
  `uvm_object_utils(alert_handler_entropy_stress_vseq)

  `uvm_object_new

  rand bit [7:0] forced_mask_val;
  rand int num_pings;

  constraint valid_mask_val_c {
    forced_mask_val >= 'h7;
    $onehot(32'(forced_mask_val) + 1) == 1;
  }

  constraint num_pings_c {
    if (forced_mask_val > 'hf0) {
      num_pings inside {[1 : 2]};
    } else {
      num_pings inside {[1 : 3]};
    }
  }

  virtual task pre_start();
    `DV_CHECK_RANDOMIZE_FATAL(this)
    cfg.alert_handler_vif.set_wait_cyc_mask(forced_mask_val);

    foreach (cfg.alert_host_cfg[i]) begin
      cfg.alert_host_cfg[i].alert_delay_max = 0;
      cfg.alert_host_cfg[i].ping_delay_max = 0;
    end
    super.pre_start();
  endtask

  task body();
    bit [NUM_LOCAL_ALERTS-1:0][NUM_ALERT_CLASSES-1:0] loc_alert_class;

    foreach (loc_alert_class[i]) loc_alert_class[i] = 1;

    `uvm_info(`gfn, "Test started", UVM_LOW)

    run_esc_rsp_seq_nonblocking();

    alert_handler_init(.intr_en('1),                       // Enable all interrupts
                       .alert_en('1),                      // Enable all alerts
                       .alert_class(0),                    // Set all alerts to class A
                       .loc_alert_en('1),                  // Enable all local alerts
                       .loc_alert_class(loc_alert_class)); // Set all local alerts to class B

    // Enable all classes and lock them.
    alert_handler_rand_wr_class_ctrl('1, '1);

    // Enable ping timer.
    csr_wr(.ptr(ral.ping_timer_en_shadowed), .value(1));

    // Lock alerts and configurations.
    alert_handler_wr_regwen_regs(.regwen(0),
                                 .alert_regwen(0),
                                 .loc_alert_regwen(0),
                                 .ping_timer_regwen(0),
                                 .class_regwen(0));

    // Wait for all alerts to be pinged at least once.
    fork begin : isolation_fork
      int num_alerts = NUM_ALERTS;
      for (int i = 0; i < NUM_ALERTS; i++) begin
        automatic int index = i;
        fork begin
          repeat (num_pings) cfg.alert_host_cfg[index].vif.wait_alert_ping();
          num_alerts--;
          `uvm_info(`gfn, $sformatf("alert %0d received %0d ping request.\n %0d alerts remaining.",
                    index, num_pings, num_alerts), UVM_LOW);
        end join_none
      end
      wait fork;
    end join

    cfg.clk_rst_vif.wait_clks($urandom_range(50, 500));

    // Check no error or local alerts triggered.
    foreach (ral.alert_cause[i]) begin
      csr_rd_check(.ptr(ral.alert_cause[i]), .compare_value(0));
    end
    foreach (ral.loc_alert_cause[i]) begin
      csr_rd_check(.ptr(ral.loc_alert_cause[i]), .compare_value(0));
    end

    // Wait some random delays, then release the force signal, issue reset.
    // This will allow the test to pass ok_to_end check from alert/esc_monitors and
    // push_pull_agent.
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 5));
    cfg.alert_handler_vif.release_wait_cyc_mask();
    dut_init();
  endtask

endclass : alert_handler_entropy_stress_vseq
