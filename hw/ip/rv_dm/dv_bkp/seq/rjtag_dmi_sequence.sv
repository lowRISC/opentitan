// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class rjtag_dmi_sequence extends uvm_sequence#(rjtag_seq_item);

  `uvm_object_utils(rjtag_dmi_sequence)

  function new(string name = "rjtag_sequence");
    super.new(name);
  endfunction

  virtual task body();

    // Or, `uvm_do(req)
    //req = rjtag_seq_item::type_id::create("req");
    //wait_for_grant();
    //assert(req.randomize());
    //send_request(req);
    //wait_for_item_done();
    //get_response(rsp);
    automatic bit [31:0] rdata;
    jtag_dmi_wr('h10, 'h00000001);
    jtag_dmi_wr('h38, 'h00047000);
    jtag_dmi_wr('h39, 'h00000040);
    jtag_dmi_wr('h3c, $urandom());
    jtag_dmi_wr('h38, 'h00147000);
    jtag_dmi_wr('h39, 'h00000040);
    jtag_dmi_rd('h3c, rdata);
    jtag_dmi_rd('h3c, rdata);
  endtask

  task jtag_dmi_wr(bit [6:0] addr, bit [31:0] data);
    `uvm_create(req)
    req.dmi_addr = addr;
    req.dmi_wr = 1'b1;
    req.dmi_wdata = data;
    `uvm_send(req)
  endtask : jtag_dmi_wr

  task jtag_dmi_rd(bit [6:0] addr, bit [31:0] data);
    `uvm_create(req)
    req.dmi_addr = addr;
    req.dmi_wr = 1'b0;
    req.dmi_wdata = '0;
    `uvm_send(req)
    data = req.dmi_rdata;
  endtask : jtag_dmi_rd

endclass
