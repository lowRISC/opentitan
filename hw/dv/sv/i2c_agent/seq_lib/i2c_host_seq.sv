// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_host_seq extends i2c_base_seq;
  `uvm_object_utils(i2c_host_seq)

  `uvm_object_new

  task body();
    req = i2c_item::type_id::create("req");
    start_item(req);
    finish_item(req);
    get_response(rsp);
  endtask : body

endclass : i2c_host_seq
