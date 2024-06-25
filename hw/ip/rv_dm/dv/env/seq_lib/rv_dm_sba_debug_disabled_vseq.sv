// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_sba_debug_disabled_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_sba_debug_disabled_vseq)
  `uvm_object_new

  // This overrides a constraint in the base vseq: we want to ensure that debug is *not* enabled for
  // this vseq.
  constraint debug_enabled_c {
    lc_hw_debug_en == 1'b0;
  }

  task body();
    sba_tl_device_seq_start();
    repeat (10) begin
      sba_access_item sba_req = sba_access_item::type_id::create("sba_req");
      `DV_CHECK_RANDOMIZE_FATAL(sba_req);
      cfg.debugger.sba_access(sba_req);
    end
    sba_tl_device_seq_stop();
  endtask

endclass
