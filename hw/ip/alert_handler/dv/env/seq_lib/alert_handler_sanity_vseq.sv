// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class alert_handler_sanity_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_sanity_vseq)

  `uvm_object_new

  rand bit[3:0] intr_en;

  // temp disable
  constraint only_enable_intr_class_a_c {
    intr_en inside {0, 1};
  }

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.classa_ctrl,
                                     lock.value == 1'b0;
                                     map_e0.value inside {[0:NUM_ALERT_HANDLER_CLASSES-1]};
                                     map_e1.value inside {[0:NUM_ALERT_HANDLER_CLASSES-1]};
                                     map_e2.value inside {[0:NUM_ALERT_HANDLER_CLASSES-1]};
                                     map_e3.value inside {[0:NUM_ALERT_HANDLER_CLASSES-1]};
                                    )
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d: intr_en=%0b", i, num_trans, intr_en),
                UVM_LOW)
      `uvm_info(`gfn, ral.classa_ctrl.sprint(), UVM_HIGH)
      alert_handler_init(.intr_en(intr_en), .classA_ctrl(ral.classa_ctrl.get()));
      drive_alert(0);
      if (intr_en != 0) begin
        wait(cfg.intr_vif.pins[0] === 1'b1);
        check_interrupts(.interrupts((1)), .check_set(1'b1));
      end else begin
        csr_spinwait(.ptr(ral.intr_state.classa), .exp_data(1'b1));
        csr_wr(.csr(ral.intr_state), .value(1));
      end
      // TODO: check escalation phases once the escalation agent is connected
      if (ral.classa_ctrl.en_e0.get() | ral.classa_ctrl.en_e1.get() |
          ral.classa_ctrl.en_e2.get() | ral.classa_ctrl.en_e3.get()) begin
        clear_esc();
      end
    end
  endtask : body

endclass : alert_handler_sanity_vseq
