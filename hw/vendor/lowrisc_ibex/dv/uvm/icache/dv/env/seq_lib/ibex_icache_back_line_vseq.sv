// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_back_line_vseq extends ibex_icache_base_vseq;

  `uvm_object_utils(ibex_icache_back_line_vseq)
  `uvm_object_new

  virtual task pre_start();
    uvm_factory        f;
    uvm_object_wrapper wrapper;
    string             base_name, back_name, old_name, inst_path;

    // The base class creates a sequence for the core and memory agents in its pre_start method. We
    // want to override its decision and use a different sequence for the core. To do so, we use the
    // factory's set_inst_override_by_name. Once we've called the base class's pre_start method, we
    // tidy up the override again (to allow sequence chaining).
    f = uvm_factory::get();
    base_name = ibex_icache_core_base_seq::type_name;
    back_name = ibex_icache_core_back_line_seq::type_name;
    inst_path = {`gfn, ".*"};

    wrapper = f.find_override_by_name(base_name, inst_path);
    old_name = (wrapper == null) ? base_name : wrapper.get_type_name();
    f.set_inst_override_by_name(base_name, back_name, inst_path);

    super.pre_start();

    f.set_inst_override_by_name(base_name, old_name, inst_path);

  endtask : pre_start

endclass : ibex_icache_back_line_vseq
