// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_stress_vseq extends mbx_base_vseq;

  `uvm_object_utils(mbx_stress_vseq)

  // Constrain the iteration and transaction counts to produce a longer stress test and,
  // importantly, perform multiple request and responses without an intervening block reset.
  constraint num_iters_c { num_iters inside {[5:10]}; }
  constraint num_txns_c { num_txns inside {[2:20]}; }



  function new(string name = "mbx_stress_vseq");
    super.new(name);
  endfunction : new

  virtual task body();
    `uvm_info(get_full_name(), "body -- stress test -- Start", UVM_DEBUG)

    super.body();
    `uvm_info(get_full_name(), "body -- stress test -- End", UVM_DEBUG)
  endtask : body

endclass : mbx_stress_vseq
