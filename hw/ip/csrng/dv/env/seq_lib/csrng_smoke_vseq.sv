// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class csrng_smoke_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_smoke_vseq)
  `uvm_object_new

  csrng_item   cs_item;

  task body();
    super.body();

    cs_item = csrng_item::type_id::create("cs_item");

    // Create/Write CSRNG Cmd_Req - Instantiate Command
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cs_item,
                                   cs_item.acmd  == csrng_pkg::INS;
                                   cs_item.flags == MuBi4True;
                                   cs_item.clen  == 4'hc;)
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Create/Write CSRNG Cmd_Req - Generate Command
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Check internal state
    if (cfg.check_int_state) begin
      for (int i = 0; i < NUM_HW_APPS + 1; i++)
        cfg.check_internal_state(.app(i), .compare(1));
    end
  endtask : body
endclass : csrng_smoke_vseq
