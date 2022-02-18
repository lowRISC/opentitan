// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence to drive instruction and / or the data register via JTAG.
class jtag_base_seq extends dv_base_seq #(
    .REQ         (jtag_item),
    .CFG_T       (jtag_agent_cfg),
    .SEQUENCER_T (jtag_sequencer)
  );

  `uvm_object_utils(jtag_base_seq)

  rand uint ir_len;
  rand logic [JTAG_IRW-1:0] ir;

  rand uint dr_len;
  rand logic [JTAG_DRW-1:0] dr;

  constraint ir_len_c {
    ir_len <= JTAG_IRW;
  }

  constraint dr_len_c {
    ir_len <= JTAG_DRW;
  }

  `uvm_object_new

  virtual task body();
    req = jtag_item::type_id::create("req");
    start_item(req);
    randomize_req(req);
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, $sformatf("rcvd response:\n%0s", rsp.sprint()), UVM_HIGH)
  endtask

  virtual function void randomize_req(jtag_item req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        ir_len == local::ir_len;
        ir     == local::ir;
        dr_len == local::dr_len;
        dr     == local::dr;
    )
  endfunction
endclass

// Constrain the base seq to only send IR.
class jtag_ir_seq extends jtag_base_seq;
  `uvm_object_utils(jtag_ir_seq)
  `uvm_object_new

  constraint dr_len_0_c {
    dr_len == 0;
  }
endclass

// Constrain the base seq to only send DR.
class jtag_dr_seq extends jtag_base_seq;
  `uvm_object_utils(jtag_dr_seq)
  `uvm_object_new

  constraint ir_len_0_c {
    ir_len == 0;
  }
endclass
