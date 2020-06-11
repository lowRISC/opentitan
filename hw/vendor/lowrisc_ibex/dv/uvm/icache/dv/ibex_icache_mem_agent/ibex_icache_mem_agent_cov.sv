// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_mem_agent_cov
  extends dv_base_agent_cov #(.CFG_T (ibex_icache_mem_agent_cfg));

  `uvm_component_utils(ibex_icache_mem_agent_cov)

  // the base class provides the following handles for use:
  // ibex_icache_mem_agent_cfg: cfg

  // Spot the gnt and pmp_err signal being high at the same time (the error should take precedence).
  // This is sampled when gnt is high and tracks whether pmp_err is high too.
  covergroup gnt_err_cg with function sample(bit pmp_err);
    coverpoint pmp_err;
  endgroup : gnt_err_cg

  function new(string name, uvm_component parent);
    super.new(name, parent);
    gnt_err_cg = new();
  endfunction : new

endclass
