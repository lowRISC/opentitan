// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_flash_seq extends spi_base_seq;
  `uvm_object_utils(spi_host_flash_seq)
  `uvm_object_new

  rand bit write_command;
  rand bit [7:0] opcode;
  rand bit [7:0] address_q[$];
  rand bit [7:0] payload_q[$];
  rand bit [7:0] read_bsize;
  rand bit [2:0] num_lanes;

  virtual task body();
    req = spi_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                   item_type == SpiFlashTrans;
                                   write_command == local::write_command;
                                   opcode == local::opcode;
                                   address_q.size() == local::address_q.size();
                                   foreach (address_q[i]) {
                                     address_q[i] == local::address_q[i];
                                   }
                                   read_bsize == local::read_bsize;
                                   num_lanes == local::num_lanes;
                                   payload_q.size() == local::payload_q.size();
                                   foreach (payload_q[i]) {
                                     payload_q[i] == local::payload_q[i];
                                   })
    finish_item(req);
    get_response(rsp);
  endtask

endclass
