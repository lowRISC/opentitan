// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A dmi access sequence to drive a single CSR read or write
class jtag_dmi_access_seq extends jtag_base_seq;

  rand bit [DMI_OPW-1:0]   op;
  rand bit [DMI_DATAW-1:0] data;
  rand bit [DMI_ADDRW-1:0] addr;

  `uvm_object_utils(jtag_dmi_access_seq)
  `uvm_object_new

  virtual task body();
    req = jtag_item::type_id::create("req");
    start_item(req);
    randomize_req(req);
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, $sformatf("rcvd response:\n%0s", rsp.sprint()), UVM_HIGH)
  endtask

  virtual function randomize_req(jtag_item req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        ir_len == DMI_IRW;
        dr_len == DMI_DRW;
        op     == local::op;
        data   == local::data;
        addr   == local::addr;
        write  == (local::op == DmiWrite) ? 1 : 0;
        dr     == {local::addr, local::data, local::op};
        ir     == JtagDmiAccess;
    )
  endfunction
endclass
