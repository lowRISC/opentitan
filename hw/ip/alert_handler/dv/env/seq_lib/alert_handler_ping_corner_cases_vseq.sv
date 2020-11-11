// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence test corner cases for alert or escalation pings:
// 1). ping integrity fail or timeout
// 2). ping interrupted by a reset signal
// 3). escalation ping interrupted by real escalation signal (this could happen because escalation
//     ping and real escalation share the same esc_p/n signals)

class alert_handler_ping_corner_cases_vseq extends alert_handler_entropy_vseq;
  `uvm_object_utils(alert_handler_ping_corner_cases_vseq)

  `uvm_object_new

  rand uint num_ping_trans;

  constraint num_ping_trans_c {
    num_ping_trans inside {[50:100]};
  }

  // always enable clr_en to hit the case when escalation ping interrupted by real esc sig
  constraint clr_and_lock_en_c {
    clr_en      == '1;
    lock_bit_en == 0;
  }

  constraint esc_accum_thresh_c {
    foreach (accum_thresh[i]) {accum_thresh[i] == 0};
  }

  constraint sig_int_c {
    esc_int_err == '1;
    esc_standalone_int_err dist {0 :/ 9, [1:'1] :/ 1};
  }

  constraint ping_fail_c {
    alert_ping_timeout == '1;
    esc_ping_timeout   == '1;
  }

  constraint ping_timeout_cyc_c {
    ping_timeout_cyc inside {[1:MAX_PING_TIMEOUT_CYCLE]};
  }

  // disable interrupt timeout
  constraint esc_intr_timeout_c {
    foreach (intr_timeout_cyc[i]) {intr_timeout_cyc[i] == 0;}
  }

  virtual task pre_start();
    super.pre_start();
    num_ping_trans.rand_mode(0);
    do_alert_handler_init = 1;
    do_standalone_alert_handler_init = 0;
    do_clear_all_interrupts = 0;
    // disable alert/esc build-in coverage, because this test forced original design variable
    for (int i = 0; i < NUM_ALERTS; i++) cfg.alert_host_cfg[i].en_cov = 0;
    for (int i = 0; i < NUM_ESCS; i++)   cfg.esc_device_cfg[i].en_cov = 0;
  endtask

  virtual task body();
    trigger_non_blocking_seqs();
    `uvm_info(`gfn, $sformatf("num_trans=%0d", num_trans), UVM_LOW)
    for (int trans = 1; trans <= num_ping_trans; trans++) begin
      int ping_index;
      `uvm_info(`gfn, $sformatf("start ping_seq %0d/%0d", trans, num_ping_trans), UVM_LOW)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_trans)
      fork begin
        fork
          begin : run_normal_sequence
            run_smoke_seq();
          end
          begin : wait_for_ping
            wait_alert_esc_ping(ping_index);
            `uvm_info(`gfn, $sformatf("ping %0d triggered", ping_index), UVM_MEDIUM);
          end
        join_any
        csr_utils_pkg::wait_no_outstanding_access();
        disable fork;
        if (ping_index > 0) run_ping_interrupt_seqs(ping_index);
      end
      join
    end
  endtask : body

  // if a ping signal is detected, this task will randomly react in these three ways:
  // 1). Interrupt the ping with a reset
  // 2). Interrupt the ping with real alerts
  // 3). Do nothing, wait until ping is done
  virtual task run_ping_interrupt_seqs(int ping_index);
    randcase
      1: begin
        `uvm_info(`gfn, "apply hard reset", UVM_MEDIUM)
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 4));
        dut_init("HARD");
      end
      40: begin
        `uvm_info(`gfn, "insert alerts", UVM_MEDIUM)
        drive_alert('1, 0);
      end
      10: begin
        `uvm_info(`gfn, "do nothing", UVM_MEDIUM)
      end
    endcase
  endtask

endclass : alert_handler_ping_corner_cases_vseq
