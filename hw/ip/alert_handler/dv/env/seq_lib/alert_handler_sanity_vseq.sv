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
  rand bit do_wr_phases_cyc;
  rand int max_phase_cyc;

  constraint wr_phases_cyc_c {
    do_wr_phases_cyc == 0;
  }

  constraint enable_one_alert_c {
    $onehot(alert_en);
  }

  constraint max_phase_cyc_c {
    max_phase_cyc inside {[0:1_000]};
  }

  task body();
    run_esc_rsp_seq_nonblocking();
    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.classa_ctrl, lock.value == 1'b0;)
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d: intr_en=%0b, alert=%0b, alert_en=%0b",
                                i, num_trans, intr_en, alert_trigger, alert_en), UVM_LOW)
      `uvm_info(`gfn, ral.classa_ctrl.sprint(), UVM_HIGH)
      alert_handler_init(.intr_en(intr_en), .alert_en(alert_en),
                         .classA_ctrl(ral.classa_ctrl.get()));

      if (do_wr_phases_cyc) wr_phases_cycle(max_phase_cyc);

      drive_alert(alert_trigger);

      if (alert_en & alert_trigger) begin
        if (intr_en[0] != 0) begin
          wait(cfg.intr_vif.pins[0] === 1'b1);
          check_interrupts(.interrupts((1)), .check_set(1'b1));
        end else begin
          csr_spinwait(.ptr(ral.intr_state.classa), .exp_data(1'b1));
          csr_wr(.csr(ral.intr_state), .value(1));
        end
      end
      // TODO: need to support multi-class
      if (ral.classa_ctrl.en.get_mirrored_value() & (
          ral.classa_ctrl.en_e0.get_mirrored_value() | ral.classa_ctrl.en_e1.get_mirrored_value() |
          ral.classa_ctrl.en_e2.get_mirrored_value() | ral.classa_ctrl.en_e3.get_mirrored_value()))
          begin
        wait_alert_handshake_finish();
        clear_esc();
      end
      read_alert_cause();
    end
  endtask : body

endclass : alert_handler_sanity_vseq
