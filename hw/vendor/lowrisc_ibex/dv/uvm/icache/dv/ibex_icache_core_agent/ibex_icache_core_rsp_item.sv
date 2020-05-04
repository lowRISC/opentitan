// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_rsp_item extends uvm_sequence_item;

  // A sequence item that is used for responses from the driver back to the sequence. This is needed
  // so that we can spot when there was an error signalled by the core (which means the next
  // sequence item will need to be a branch).

  bit saw_error;

  `uvm_object_utils_begin(ibex_icache_core_rsp_item)
    `uvm_field_int (saw_error, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
