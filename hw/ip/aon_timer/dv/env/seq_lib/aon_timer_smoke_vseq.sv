// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class aon_timer_smoke_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_smoke_vseq)

  `uvm_object_new

  task body();
    // Register Read from the thresholds
    bit [31:0] wkup_thold;
    bit [31:0] bark_thold;
    bit [31:0] bite_thold;

    aon_timer_init();
    csr_utils_pkg::csr_rd(.ptr(ral.wkup_thold), .value(wkup_thold));
    `uvm_info(`gfn,
              $sformatf("\n\t ---| reading 0x%0h from WKUP_THOLD", wkup_thold),
              UVM_HIGH)

    csr_utils_pkg::csr_rd(.ptr(ral.wdog_bark_thold), .value(bark_thold));
    `uvm_info(`gfn,
              $sformatf("\n\t ---| reading 0x%0h from WDOG_BARK_THOLD", bark_thold),
              UVM_HIGH)

    csr_utils_pkg::csr_rd(.ptr(ral.wdog_bite_thold), .value(bite_thold));
    `uvm_info(`gfn,
              $sformatf("\n\t ---| reading 0x%0h from WDOG_BITE_THOLD", bite_thold),
              UVM_HIGH)

    `uvm_info(`gfn, "\n\t ----| Waiting for AON Timer to finish (interrupt)", UVM_LOW)
    wait_for_interrupt();
    aon_timer_shutdown();
  endtask : body

endclass : aon_timer_smoke_vseq
