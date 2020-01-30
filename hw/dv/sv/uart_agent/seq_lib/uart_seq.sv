// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_seq extends uart_base_seq;
  `uvm_object_utils(uart_seq)

  rand bit [7:0] data;
  rand bit       parity_err;
  rand bit       parity;
  rand bit       frame_err;

  constraint parity_c {
    if (parity_err) {
      parity != `GET_PARITY(data, p_sequencer.cfg.odd_parity);
    } else {
      parity == `GET_PARITY(data, p_sequencer.cfg.odd_parity);
    }
  }
  `uvm_object_new

  task body();
    `uvm_info(`gfn, $sformatf("starting uart rx byte xfer seq: 0x%0h", data), UVM_HIGH)
    req = uart_item::type_id::create("req");
    start_item(req);
    req.stop_bit_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        data     == local::data;
        parity   == local::parity;
        stop_bit == !frame_err;
        )
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "uart rx byte xfer done", UVM_HIGH)
  endtask

endclass : uart_seq
