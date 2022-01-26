// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class aon_timer_smoke_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_smoke_vseq)
  `uvm_object_new

  task body();

    aon_timer_init();
    smoke_configure();
    wait_for_interrupt();
    aon_timer_shutdown();

  endtask : body

  task smoke_configure();

    `uvm_info(`gfn, "Enabling AON Timer. Writing 1 to WKUP_CTRL and WDOG_CTRL", UVM_HIGH)
    csr_utils_pkg::csr_wr(ral.wkup_ctrl.enable, 1'b1);
    csr_utils_pkg::csr_wr(ral.wdog_ctrl.enable, 1'b1);

    `uvm_info(`gfn, "\n\t Waiting for AON Timer to finish (interrupt)", UVM_HIGH)
  endtask : smoke_configure


endclass : aon_timer_smoke_vseq
