// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class host_socket1n_seq_item extends xbar_seq_item;
  constraint addr_range  { addr[31:30] dist { 0:=1, 1:=1, 2:=1, 3:= 1}; }
  constraint wstrb_fixed { wstrb == 'hF; }
endclass : host_socket1n_seq_item

class host_socket1n_seq extends xbar_seq_base;

  function new(string name);
    super.new(name);
  endfunction : new

  task body();
    host_socket1n_seq_item item;
    xbar_seq_item item_rsp;
    xbar_seq_item item_cmp;

    int trial;
    mailbox #(xbar_seq_item) cmpbox;
    cmpbox = new;

    // Response handling
    fork
      forever begin
        cmpbox.get(item_cmp);
        super.rsp.get(item_rsp); // Write
        super.rsp.get(item_rsp); // Read
        assert (item_cmp.data == item_rsp.data)
          else $error("Data mismatch: ADDR(0x%08x) EXP(0x%08x) GOT(0x%08x)",
            item_cmp.addr,
            item_cmp.data,
            item_rsp.data);
      end
    join_none

    trial = $urandom_range(100,200);

    for (int i = 0 ; i < trial ; i++) begin
      item = new;
      void'(item.randomize());
      this.write_req(item.addr, item.data, '1);
      this.read_req(item.addr);
      cmpbox.put(item);
    end
  endtask : body

endclass
