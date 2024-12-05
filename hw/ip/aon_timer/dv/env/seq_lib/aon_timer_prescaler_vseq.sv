// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// prescaler test vseq
class aon_timer_prescaler_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_prescaler_vseq)

  // Randomize prescaler configuration of the wake up timer.
  randc bit [11:0] prescaler;

  //Overrides constraint in parent vseq:
  extern constraint thold_count_c;

  extern function new (string name="");
  extern task body();
  extern task prescaler_configure();

endclass : aon_timer_prescaler_vseq

constraint aon_timer_prescaler_vseq::thold_count_c {
  wkup_thold      inside {[1:2]};
  wdog_bark_thold inside {[1:2]};
  wdog_bite_thold inside {[1:2]};
  wkup_count == 0;
  wdog_count == 0;
}

function aon_timer_prescaler_vseq::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_prescaler_vseq::body();
  aon_timer_init();
  prescaler_configure();
  wait_for_interrupt();
  aon_timer_shutdown();
endtask : body

task aon_timer_prescaler_vseq::prescaler_configure();

  // Write random value to the prescaler
  csr_utils_pkg::csr_wr(ral.wkup_ctrl.prescaler, prescaler);
  `uvm_info(`gfn,
            $sformatf("\n\t Writing random prescaler value of %d to WKUP CTRL", prescaler),
            UVM_HIGH)


  `uvm_info(`gfn, "Enabling AON Timer (WKUP ONLY). Writing 1 to WKUP_CTRL", UVM_HIGH)
  csr_utils_pkg::csr_wr(ral.wkup_ctrl.enable, 1'b1);
  csr_utils_pkg::csr_wr(ral.wdog_ctrl.enable, 1'b0);

  `uvm_info(`gfn, "\n\t Waiting for AON Timer to finish (interrupt)", UVM_HIGH)
endtask : prescaler_configure
