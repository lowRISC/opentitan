// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// --------------------
// Device sequence
// --------------------
class spi_device_seq extends spi_base_seq;

  `uvm_object_utils(spi_device_seq)
  `uvm_object_new

  spi_item req_q[$];

  virtual task body();
    req = spi_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(req)
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, $sformatf("\n  received response: %0s", rsp.sprint()), UVM_HIGH)
  endtask
endclass : spi_device_seq