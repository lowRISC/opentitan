// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_agent_cov extends dv_base_agent_cov #(reset_agent_cfg);
  `uvm_component_utils(reset_agent_cov)

  // Class should extends uvm_subscriber #(reset_item), not sure what to do here
  // Option 1: class reset_agent_cov extends uvm_subscriber #(reset_item);
  // Option 2: declare the following and extend dv_base_agent_cov
  // typedef uvm_subscriber #(reset_item) this_type;
  uvm_analysis_imp #(reset_item, reset_agent_cov) analysis_imp;

  int unsigned reset_cnt;   // Number of resets generated

  // Internal use only
  protected int unsigned assert_delay;
  protected int unsigned assert_width;

  covergroup cg_assert_lengths;
    cp_assert_delay: coverpoint assert_delay {
      bins bin_zero   = {0};
      bins bin_one    = {1};
      bins bin_short  = {[2:100]};
      bins bin_long   = {[101:$]};
    }

    cp_assert_width: coverpoint assert_width {
      bins bin_one    = {1};
      bins bin_short  = {[2:100]};
      bins bin_long   = {[101:$]};
    }
  endgroup : cg_assert_lengths

  covergroup cg_reset_cfg;
    cp_assert_sync  : coverpoint cfg.assert_is_sync;
    cp_deassert_sync: coverpoint cfg.deassert_is_sync;
    cp_polarity     : coverpoint cfg.polarity;
    cross_reset_cfg : cross cp_assert_sync, cp_deassert_sync, cp_polarity;
  endgroup : cg_reset_cfg

  covergroup cg_reset_moments;
    cp_reset_cnt: coverpoint reset_cnt {
      bins bin_initial      = {1};
      bins bin_intermediate = {[2:$]};
    }
  endgroup : cg_reset_moments

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent = null);
  extern function void write(reset_item t);
endclass : reset_agent_cov


function reset_agent_cov::new(string name, uvm_component parent = null);
  super.new(name, parent);
  analysis_imp      = new ("analysis_imp", this);
  cg_assert_lengths = new();
  cg_reset_cfg      = new();
  cg_reset_moments  = new();
  reset_cnt         = 0;
endfunction : new

// This method is called from the monitor when broadcasting the transaction
function void reset_agent_cov::write(reset_item t);
  reset_cnt++;
  assert_delay  = t.assert_delay;
  assert_width  = t.assert_width;

  cg_assert_lengths.sample();
  cg_reset_cfg.sample();
  cg_reset_moments.sample();
endfunction : write
