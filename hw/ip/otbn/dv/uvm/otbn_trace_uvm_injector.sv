// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A tiny fragment that grabs an otbn_trace_if interface and injects it into the UVM config
// database. We can't do this directly in the testbench, because the interface itself is bound into
// the DUT with a bind statement, so can't be accessed with a hierarchical reference.
//
// Instead, the testbench binds this module in to the DUT as well, allowing it to grab the trace
// interface.

module otbn_trace_uvm_injector(otbn_trace_if otbn_trace);
  initial begin
    uvm_config_db#(virtual otbn_trace_if)::set(null, "*.env", "trace_vif", otbn_trace);
  end
endmodule
