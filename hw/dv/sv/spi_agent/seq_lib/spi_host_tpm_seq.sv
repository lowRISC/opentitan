// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_tpm_seq extends spi_base_seq;
  local bit [7:0] address_q[$];
  rand bit [TPM_ADDR_WIDTH-1:0] addr;
  rand bit [7:0] data_q[$];
  rand int       read_size;
  rand int       write_command;

  bit [CSB_WIDTH-1:0] csb_sel = 0;

  constraint write_command_and_data_c {
    if (write_command) {
      read_size == 0;
    } else {
      data_q.size == 0;
    }
  }

  `uvm_object_utils_begin(spi_host_tpm_seq)
    `uvm_field_int(addr,            UVM_DEFAULT)
    `uvm_field_int(write_command,   UVM_DEFAULT)
    `uvm_field_int(read_size,       UVM_DEFAULT)
    `uvm_field_int(csb_sel,         UVM_DEFAULT)
    `uvm_field_queue_int(data_q,    UVM_DEFAULT)
    `uvm_field_queue_int(address_q, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  virtual task body();
    // MSB byte sent first
    repeat (TPM_ADDR_WIDTH_BYTE) begin
      address_q.push_front(addr[7:0]);
      addr = addr >> 8;
    end
    req = spi_item::type_id::create("req");
    start_item(req);

    cfg.spi_func_mode = SpiModeTpm;

    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                   item_type == SpiTransNormal;
                                   csb_sel == local::csb_sel;
                                   write_command == local::write_command;
                                   address_q.size() == local::address_q.size();
                                   foreach (address_q[i]) {
                                     address_q[i] == local::address_q[i];
                                   }
                                   payload_q.size() == 0; // no used for tpm
                                   data.size == local::data_q.size();
                                   foreach (data_q[i]) {
                                     data[i] == local::data_q[i];
                                   }
                                   read_size == local::read_size;)
    finish_item(req);
    get_response(rsp);
  endtask

endclass
