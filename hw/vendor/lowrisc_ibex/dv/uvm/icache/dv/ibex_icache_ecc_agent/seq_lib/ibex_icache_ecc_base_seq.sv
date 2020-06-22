// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_ecc_base_seq
  extends dv_base_seq #(.REQ         (ibex_icache_ecc_item),
                        .CFG_T       (ibex_icache_ecc_agent_cfg),
                        .SEQUENCER_T (ibex_icache_ecc_sequencer));
  `uvm_object_utils(ibex_icache_ecc_base_seq)

  `uvm_object_new

  virtual task body();
    forever begin
      req = ibex_icache_ecc_item::type_id::create("req");
      start_item(req);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                     req.delay dist {0       :/ 1,
                                                     [1:20]  :/ 1,
                                                     [21:50] :/ 1};)
      finish_item(req);
    end
  endtask

endclass
