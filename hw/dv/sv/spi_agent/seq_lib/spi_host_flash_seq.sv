// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_flash_seq extends spi_base_seq;

  rand bit [7:0] op_code;
  rand bit [7:0] address_q[$];
  rand bit [7:0] payload_q[$];
  rand int          read_size;

  `uvm_object_utils_begin(spi_host_flash_seq)
    `uvm_field_int(op_code,         UVM_DEFAULT)
    `uvm_field_int(read_size,       UVM_DEFAULT)
    `uvm_field_queue_int(payload_q, UVM_DEFAULT)
    `uvm_field_queue_int(address_q, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  virtual task body();
    req = spi_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                   item_type == SpiFlashTrans;
                                   opcode == local::op_code;
                                   write_command == cfg.cmd_infos[op_code].write_command;
                                   address_q.size() == cfg.cmd_infos[op_code].addr_bytes;
                                   foreach (address_q[i]) {
                                     address_q[i] == local::address_q[i];
                                   }
                                   num_lanes == cfg.cmd_infos[op_code].num_lanes;
                                   if (write_command) {
                                     read_size == 0;
                                     payload_q.size() == local::payload_q.size();
                                     foreach (payload_q[i]) {
                                       payload_q[i] == local::payload_q[i];
                                     }
                                   } else { // read
                                     read_size == local::read_size;
                                     payload_q.size() == 0;
                                   })
    finish_item(req);
    get_response(rsp);
  endtask

endclass
