// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_host_seq extends csrng_base_seq;
  `uvm_object_utils(csrng_host_seq)

  `uvm_object_new

  task body();
    req = csrng_item::type_id::create("req");
    start_item(req);
    finish_item(req);
    get_response(rsp);
  endtask

endclass
