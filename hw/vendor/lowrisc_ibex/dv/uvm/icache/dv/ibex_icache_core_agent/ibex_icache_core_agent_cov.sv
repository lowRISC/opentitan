// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_agent_cov extends dv_base_agent_cov #(ibex_icache_core_agent_cfg);
  `uvm_component_utils(ibex_icache_core_agent_cov)

  // the base class provides the following handles for use:
  // ibex_icache_core_agent_cfg: cfg

  // A covergroup that spots a pair of fetches with no intermediate branch.
  //
  // addr1 will always be addr0 + 2 or addr0 + 4 (possibly with a wraparound), depending on the
  // contents of the first fetch.
  //
  // We want to see both increments, and also a wrap-around.
  covergroup inc_fetch_cg with function sample (bit compressed, bit wraparound);
    cmp:  coverpoint compressed;
    wrap: coverpoint wraparound;
    all:  cross cmp, wrap;
  endgroup : inc_fetch_cg

  // Branch destinations, binned into "near zero", "near top" and "the rest"
  covergroup branch_dest_cg with function sample (bit [31:0] addr);
    coverpoint addr {
      bins zero = { 0 };
      bins low  = { [2:16] };
      bins high = { [32'hfffffff0:32'hfffffffc] };
      bins top  = { 32'hfffffffe };
      bins mid  = default;
    }
  endgroup : branch_dest_cg

  // A covergroup tracking properties of fetches.
  covergroup fetch_cg with function sample (bit err, bit err_plus2, bit enable);
    coverpoint enable;
    coverpoint err;
    coverpoint err_plus2;

    // Cross err with err_plus2: the latter only has any effect when err is true, so we should make
    // sure we see the combination. Bin together (False, False) and (False, True) because they have
    // the same meaning.
    errs: cross err, err_plus2 {
      bins no_err = binsof(err) intersect {0};
    }
  endgroup : fetch_cg

  // Tracking when a branch cancels a valid result, recording whether or not this happens at the
  // same time as ready is high.
  covergroup cancelled_valid_cg with function sample (bit ready);
    coverpoint ready;
  endgroup : cancelled_valid_cg

  // Track the combination of branch_spec and branch. The branch signal implies branch_spec, but the
  // converse is not true. This covergroup is sampled when branch_spec is high.
  covergroup branch_spec_cg with function sample (bit branch);
    coverpoint branch;
  endgroup : branch_spec_cg

  function new(string name, uvm_component parent);
    super.new(name, parent);
    inc_fetch_cg = new();
    branch_dest_cg = new();
    fetch_cg = new();
    cancelled_valid_cg = new();
    branch_spec_cg = new();
  endfunction : new

  // Called on an "incrementing" pair of fetches: two fetches with no branch in between. addr0/addr1
  // should be the address of the first/second fetch, respectively.
  function automatic void on_inc_fetches(bit [31:0] addr0, bit [31:0] addr1);
    bit compressed = (addr1 == addr0 + 2);
    bit wrap       = addr1 < addr0;
    inc_fetch_cg.sample(compressed, wrap);
  endfunction

endclass
