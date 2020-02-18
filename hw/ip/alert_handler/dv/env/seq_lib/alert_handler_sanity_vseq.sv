// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class alert_handler_sanity_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_sanity_vseq)

  `uvm_object_new

  rand bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_en;
  rand bit [alert_pkg::NAlerts-1:0]        alert_trigger;
  rand bit [alert_pkg::NAlerts-1:0]        alert_en;
  rand bit [alert_pkg::NAlerts*2-1:0]      alert_class_map;
  rand bit do_clr_esc;
  rand bit do_wr_phases_cyc;
  rand bit do_esc_intr_timeout;
  rand bit [TL_DW-1:0] max_phase_cyc;
  rand bit [TL_DW-1:0] intr_timeout_cyc[NUM_ALERT_HANDLER_CLASSES];
  rand bit [TL_DW-1:0] accum_thresh    [NUM_ALERT_HANDLER_CLASSES];

  int      max_wait_phases_cyc = MIN_CYCLE_PER_PHASE * NUM_ESC_PHASES;

  constraint enable_one_alert_c {
    $onehot(alert_en);
  }

  constraint max_phase_cyc_c {
    max_phase_cyc inside {[0:1_000]};
  }

  constraint enable_classa_only_c {
    alert_class_map == 0; // all the alerts assign to classa
  }

  // constraint to trigger escalation
  constraint esc_accum_thresh_c {
    foreach (accum_thresh[i]) {soft accum_thresh[i] inside {[0:1]};}
  }

  constraint esc_intr_timeout_c {
    foreach (intr_timeout_cyc[i]) {intr_timeout_cyc[i] inside {[1:1_000]};}
  }

  task body();
    run_esc_rsp_seq_nonblocking();
    for (int i = 1; i <= num_trans; i++) begin
      bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_trigger;
      bit [TL_DW-1:0] intr_state_exp_val;
      `DV_CHECK_RANDOMIZE_FATAL(this)

      `uvm_info(`gfn,
          $sformatf("starting seq %0d/%0d: intr_en=%0b, alert=%0b, alert_en=%0b, alert_class=%0b",
          i, num_trans, intr_en, alert_trigger, alert_en, alert_class_map), UVM_LOW)
      alert_handler_init(.intr_en(intr_en), .alert_en(alert_en), .alert_class(alert_class_map));

      alert_handle_rand_wr_class_ctrl();

      if (do_wr_phases_cyc) begin
        wr_phases_cycle(max_phase_cyc);
        max_wait_phases_cyc = (max_wait_phases_cyc > (max_phase_cyc * NUM_ESC_PHASES)) ?
                               max_wait_phases_cyc : (max_phase_cyc * NUM_ESC_PHASES);
      end

      if (do_esc_intr_timeout) wr_intr_timeout_cycle(intr_timeout_cyc);
      wr_class_accum_threshold(accum_thresh);

      drive_alert(alert_trigger);

      // read and check interrupt
      if (alert_en & alert_trigger) begin
        // calculate which interrupt should be triggered
        for (int i = 0; i < alert_pkg::NAlerts; i++) begin
          if (alert_en[i] && alert_trigger[i]) begin
            intr_trigger[((alert_class_map >> i*2) & 2'b11)] = 1;
          end
        end
        if ((intr_en & intr_trigger) > '0) begin
          if (do_esc_intr_timeout) begin
            int max_intr_timeout_cyc;
            foreach (intr_timeout_cyc[i]) begin
              max_intr_timeout_cyc = (max_intr_timeout_cyc > intr_timeout_cyc[i]) ?
                                      max_intr_timeout_cyc : intr_timeout_cyc[i];
            end
            cfg.clk_rst_vif.wait_clks(max_intr_timeout_cyc);
          end
          wait(cfg.intr_vif.pins[(NUM_ALERT_HANDLER_CLASSES-1):0] == (intr_trigger & intr_en));
          check_interrupts(.interrupts(intr_trigger & intr_en), .check_set(1));
        end
        if ((~intr_en & intr_trigger) > '0) begin
          csr_spinwait(.ptr(ral.intr_state), .exp_data(~intr_en & intr_trigger));
          csr_wr(.csr(ral.intr_state), .value(~intr_en & intr_trigger));
        end
      end

      // wait to ensure all escalation phases are done before clearing the esc class
      // TODO: replace with accurate status and cycle check
      wait_alert_esc_handshake_done(max_wait_phases_cyc);
      read_alert_cause();
      if (do_clr_esc) clear_esc();
    end
  endtask : body

endclass : alert_handler_sanity_vseq
