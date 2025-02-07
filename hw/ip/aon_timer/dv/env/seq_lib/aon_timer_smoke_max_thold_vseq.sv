// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test with maximum threshold - helps close FCOV corner cases
class aon_timer_smoke_max_thold_vseq extends aon_timer_smoke_vseq;
  `uvm_object_utils(aon_timer_smoke_max_thold_vseq)

  extern constraint extra_thold_count_c;

  extern function new (string name="");

endclass : aon_timer_smoke_max_thold_vseq

function aon_timer_smoke_max_thold_vseq::new (string name="");
  super.new(name);
endfunction : new

constraint aon_timer_smoke_max_thold_vseq::extra_thold_count_c {
  wdog_bark_thold == (2**WDOG_WIDTH-1);
  wdog_bite_thold == (2**WDOG_WIDTH-1);
  wkup_thold      == (2**WKUP_WIDTH-1);
}
