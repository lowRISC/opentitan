// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register reg class which will be used to generate the reg mem
class dv_base_mem extends uvm_mem;

  function new(string           name,
               longint unsigned size,
               int unsigned     n_bits,
               string           access = "RW",
               int              has_coverage = UVM_NO_COVERAGE);
    super.new(name, size, n_bits, access, has_coverage);
  endfunction : new

endclass
