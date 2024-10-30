// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class aon_timer_smoke_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_smoke_vseq)

  extern function new (string name="");
  extern task body();
  extern task smoke_configure();

endclass : aon_timer_smoke_vseq

function aon_timer_smoke_vseq::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_smoke_vseq::body();
  aon_timer_init();
  smoke_configure();
  wait_for_interrupt();
  aon_timer_shutdown();
endtask : body

task aon_timer_smoke_vseq::smoke_configure();

  `uvm_info(`gfn, "Enabling AON Timer. Writing 1 to WKUP_CTRL and WDOG_CTRL", UVM_HIGH)
  csr_utils_pkg::csr_wr(ral.wkup_ctrl.enable, 1'b1);
  wdog_ctrl_pause_in_sleep = $urandom_range(0, 1);
  ral.wdog_ctrl.enable.set(1);
  ral.wdog_ctrl.pause_in_sleep.set(wdog_ctrl_pause_in_sleep);
  csr_update(ral.wdog_ctrl);
  `uvm_info(`gfn, "\n\t Waiting for AON Timer to finish (interrupt)", UVM_HIGH)
endtask : smoke_configure
