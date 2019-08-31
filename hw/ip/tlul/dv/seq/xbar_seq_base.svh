// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

class xbar_seq_base;

  virtual xbar_if vif;

  mailbox #(xbar_seq_item) req;
  mailbox #(xbar_seq_item) rsp;

  string name;

  function new(string name);
    this.name = name;
  endfunction : new

  task connect(mailbox #(xbar_seq_item) req,
               mailbox #(xbar_seq_item) rsp
             );
    this.req = req;
    this.rsp = rsp;
  endtask : connect

  task pre_start(virtual xbar_if xbar_if);
    this.vif = xbar_if;
  endtask : pre_start

  task run();
    // Call body
    body();
  endtask : run

  virtual task body();
    // FATAL: Need to override
  endtask : body

  task write_req(input bit [31:0] addr,
                 input bit [31:0] data,
                 input bit [3:0]  wstrb);
    xbar_seq_item item;
    item = new;
    item.addr  = addr;
    item.data  = data;
    item.wstrb = wstrb;
    item.op    = xbar_pkg::BUS_WR;
    this.req.put(item);

  endtask : write_req

  task write_rsp();
    xbar_seq_item item;
    this.rsp.get(item);
  endtask : write_rsp

  task write(input bit [31:0] addr,
             input bit [31:0] data,
             input bit [3:0]  wstrb);
    this.write_req(addr, data, wstrb);
    this.write_rsp(); // 1 outstanding
  endtask : write

  task write_async(input bit [31:0] addr,
                   input bit [31:0] data,
                   input bit [3:0]  wstrb);
    this.write_req(addr, data, wstrb);
    fork
      this.write_rsp();
    join_none
  endtask : write_async

  task read_req(input bit [31:0] addr);
    xbar_seq_item item;
    item = new;
    item.addr = addr;
    item.op   = xbar_pkg::BUS_RD;
    this.req.put(item);
  endtask : read_req

  task read_data(output bit [31:0] data);
    xbar_seq_item item;
    this.rsp.get(item);
    data = item.data;
  endtask : read_data

  task read(input  bit [31:0] addr,
            output bit [31:0] data);
    this.read_req(addr);

    this.read_data(data);
  endtask : read

  task compare(input  bit [31:0] addr,
           input  bit [31:0] data);
    logic [31:0] rdata;
    this.write_req(addr, data, '1);
    this.read_req(addr);
    this.write_rsp();
    this.read_data(rdata);
    assert(data == rdata)
      else $error("Data mismatch: ADDR(0x%08x) EXP(0x%08x) GOT(0x%08x)", addr, data, rdata);
  endtask : compare

  task compare_async(input bit [31:0] addr,
                     input bit [31:0] data);
    logic [31:0] rdata;
    this.write_req(addr, data, '1);
    this.read_req(addr);
    fork
      begin
        this.write_rsp();
        this.read_data(rdata);
        assert(data == rdata)
          else $error("Data mismatch: ADDR(0x%08x) EXP(0x%08x) GOT(0x%08x)", addr, data, rdata);
      end
    join_none
  endtask : compare_async
endclass
