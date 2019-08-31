// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class host_rand_seq_item extends xbar_seq_item;
  constraint addr_range  { addr%4 == 0; addr > 'h0 ; addr < 'h8000_0000; }
  constraint wstrb_fixed { wstrb == 'hF; }
endclass : host_rand_seq_item

class host_rand_seq extends xbar_seq_base;

  function new(string name);
    super.new(name);
  endfunction : new

  task body();
    host_rand_seq_item item_wr;
    xbar_seq_item      item_rd;
    xbar_seq_item      item_rsp;

    int trial;

    trial = $urandom_range(4,20);

    item_wr = new;
    void'(item_wr.randomize());
    item_wr.op = xbar_pkg::BUS_WR;

    super.req.put(item_wr);

    item_rd = item_wr.copy();
    item_rd.op = xbar_pkg::BUS_RD;

    super.req.put(item_rd);

    super.rsp.get(item_rsp); // for write, discard
    super.rsp.get(item_rsp);

    $display("Data received");
    assert(item_rsp.data == item_wr.data)
      else $error("Data mismatch: ADDR(0x%08x) EXP(0x%08x) GOT(0x%08x)",
      item_wr.addr, item_wr.data, item_rsp.data);

    // Try #req greater than FIFO depth
    for (int i = 0 ; i < trial ; i++) begin
      host_rand_seq_item req_item;
      req_item = new;
      void'(req_item.randomize());
      super.req.put(req_item);
    end
    // Accept
    for (int i = 0 ; i < trial ; i++) begin
      super.rsp.get(item_rsp);
    end
  endtask : body

endclass
