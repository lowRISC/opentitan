// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_back_line_vseq extends ibex_icache_base_vseq;

  `uvm_object_utils(ibex_icache_back_line_vseq)
  `uvm_object_new

  virtual task pre_start();
    // The base class creates a sequence for the core and memory agents in its pre_start method. We
    // want to override its decision and use a different sequence for the core
    ibex_icache_core_base_seq::type_id::
      set_inst_override(ibex_icache_core_back_line_seq::get_type(), "*");

    super.pre_start();
  endtask : pre_start

endclass : ibex_icache_back_line_vseq
