// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke test vseq
class alert_handler_smoke_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_smoke_vseq)

  `uvm_object_new

  rand bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_en;
  rand bit [NUM_ALERT_HANDLER_CLASSES-1:0] clr_en;
  rand bit [NUM_ALERT_HANDLER_CLASSES-1:0] lock_bit_en;
  rand bit [NUM_ALERTS-1:0]                alert_trigger;
  rand bit [NUM_ALERTS-1:0]                alert_int_err;
  rand bit [NUM_ALERTS-1:0]                alert_en;
  rand bit [NUM_ALERTS-1:0]                alert_ping_timeout;
  rand bit [NUM_ALERTS*2-1:0]              alert_class_map;
  rand bit [NUM_LOCAL_ALERT-1:0]           local_alert_en;
  rand bit [NUM_LOCAL_ALERT*2-1:0]         local_alert_class_map;
  rand bit [NUM_ESCS-1:0]                  esc_int_err;
  rand bit [NUM_ESCS-1:0]                  esc_standalone_int_err;
  rand bit [NUM_ESCS-1:0]                  esc_ping_timeout;

  rand bit do_clr_esc;
  rand bit do_wr_phases_cyc;
  rand bit do_esc_intr_timeout;
  rand bit do_lock_config;
  rand bit rand_drive_entropy;
  rand bit [TL_DW-1:0] ping_timeout_cyc;
  rand bit [TL_DW-1:0] max_phase_cyc;
  rand bit [TL_DW-1:0] intr_timeout_cyc [NUM_ALERT_HANDLER_CLASSES];
  rand bit [TL_DW-1:0] accum_thresh     [NUM_ALERT_HANDLER_CLASSES];

  int max_wait_phases_cyc = MIN_CYCLE_PER_PHASE * NUM_ESC_PHASES;
  int max_intr_timeout_cyc;
  bit do_standalone_alert_handler_init = 1;

  uvm_verbosity verbosity = UVM_LOW;

  constraint lock_bit_c {
    do_lock_config dist {1 := 1, 0 := 49};
  }

  constraint clr_and_lock_en_c {
    clr_en      dist {[0:'b1110] :/ 4, '1         :/ 6};
    lock_bit_en dist {0          :/ 6, [1:'b1111] :/ 4};
  }

  constraint enable_one_alert_c {
    $onehot(alert_en);
  }

  constraint max_phase_cyc_c {
    max_phase_cyc inside {[0:1_000]};
  }

  // set min to 32 cycles (default value) to avoid alert ping timeout due to random delay
  constraint ping_timeout_cyc_c {
    ping_timeout_cyc inside {[32:MAX_PING_TIMEOUT_CYCLE]};
  }

  constraint enable_classa_only_c {
    alert_class_map == 0; // all the alerts assign to classa
    local_alert_class_map == 0; // all local alerts assign to classa
  }

  // constraint to trigger escalation
  constraint esc_accum_thresh_c {
    foreach (accum_thresh[i]) {soft accum_thresh[i] inside {[0:1]};}
  }

  constraint esc_intr_timeout_c {
    foreach (intr_timeout_cyc[i]) {intr_timeout_cyc[i] inside {[1:1_000]};}
  }

  constraint sig_int_c {
    alert_int_err          == 0;
    esc_int_err            == 0;
    esc_standalone_int_err == 0;
  }

  constraint ping_fail_c {
    alert_ping_timeout == 0;
    esc_ping_timeout   == 0;
  }

  task body();
    fork
      begin : isolation_fork
        trigger_non_blocking_seqs();
        run_smoke_seq();
        disable fork; // disable non-blocking seqs for stress_all tests
      end // end fork
    join
  endtask : body

  virtual task trigger_non_blocking_seqs();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(esc_int_err)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(alert_ping_timeout)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(esc_ping_timeout)
    run_esc_rsp_seq_nonblocking(esc_int_err, esc_ping_timeout);
    run_alert_ping_rsp_seq_nonblocking(alert_ping_timeout);
  endtask

  virtual task run_smoke_seq();
    `uvm_info(`gfn, $sformatf("num_trans=%0d", num_trans), UVM_LOW)
    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)

      `uvm_info(`gfn,
          $sformatf("start seq %0d/%0d: intr_en=%0b, alert=%0b, alert_en=%0b, alert_class=%0b",
          i, num_trans, intr_en, alert_trigger, alert_en, alert_class_map), verbosity)

      // write initial settings (enable and mapping csrs)
      if (do_standalone_alert_handler_init) begin
        alert_handler_init(.intr_en(intr_en),
                           .alert_en(alert_en),
                           .alert_class(alert_class_map),
                           .loc_alert_en(local_alert_en),
                           .loc_alert_class(local_alert_class_map));
      end

      // write class_ctrl and clren_reg
      alert_handler_rand_wr_class_ctrl(lock_bit_en);
      alert_handler_wr_regwen_regs(clr_en);

      // randomly write phase cycle registers
      // always set phase_cycle for the first iteration, in order to pass stress_all test
      if (do_wr_phases_cyc || i == 1) wr_phases_cycle(max_phase_cyc);

      // randomly write interrupt timeout resigers and accumulative threshold registers
      if (do_esc_intr_timeout) wr_intr_timeout_cycle(intr_timeout_cyc);
      wr_class_accum_threshold(accum_thresh);
      wr_ping_timeout_cycle(ping_timeout_cyc);

      //drive entropy
      cfg.entropy_vif.drive(rand_drive_entropy);

      // when all configuration registers are set, write lock register
      lock_config(do_lock_config);

      // if config is not locked, update max_intr_timeout and max_wait_phases cycles
      if (!config_locked) begin
        bit [TL_DW-1:0] max_intr_timeout_cyc;
        bit [TL_DW-1:0] max_q[$] = intr_timeout_cyc.max();
        max_intr_timeout_cyc = max_q[0];
        max_wait_phases_cyc = max2(max_wait_phases_cyc, max_phase_cyc * NUM_ESC_PHASES);
        if (do_lock_config) config_locked = 1;
      end

      // drive esc standalone responses and alerts
      if (esc_standalone_int_err) drive_esc_rsp(esc_standalone_int_err);
      drive_alert(alert_trigger, alert_int_err);

      if (do_esc_intr_timeout) begin
        cfg.clk_rst_vif.wait_clks(max_intr_timeout_cyc);
        // this task checks three sets of registers related to alert/esc status:
        // alert_accum_cnt, esc_cnt, class_state
        read_esc_status();
      end
      // only check interrupt when no esc_int_err, otherwise clear interrupt might happen the
      // same cycle as interrupt triggered by esc_int_err
      if (esc_int_err == 0) check_alert_interrupts();

      // if ping timeout enabled, wait for ping timeout done before checking escalation phases
      if ((esc_int_err | alert_ping_timeout) > 0) cfg.clk_rst_vif.wait_clks(MAX_PING_TIMEOUT_CYCLE);

      // wait escalation done, and random interrupt with clear_esc
      wait_alert_handshake_done();
      fork
        begin
          wait_esc_handshake_done();
        end
        begin
          cfg.clk_rst_vif.wait_clks($urandom_range(0, max_wait_phases_cyc));
          if ($urandom_range(0, 1) && (esc_int_err == 0)) clear_esc();
        end
      join
      read_alert_cause();
      read_esc_status();
      if (do_clr_esc) clear_esc();
      check_alert_interrupts();
    end
  endtask

endclass : alert_handler_smoke_vseq
