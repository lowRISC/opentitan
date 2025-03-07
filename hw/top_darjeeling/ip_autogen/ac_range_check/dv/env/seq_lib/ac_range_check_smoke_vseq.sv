// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_smoke_vseq extends ac_range_check_base_vseq;
  `uvm_object_utils(ac_range_check_smoke_vseq)

  // Constraints
  extern constraint num_trans_c;
  extern constraint tmp_c;
  extern constraint range_limit_c;
  extern constraint range_racl_policy_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : ac_range_check_smoke_vseq


constraint ac_range_check_smoke_vseq::num_trans_c {
  num_trans inside {[50:100]};
}

// TODO remove this temporary directed constraint
constraint ac_range_check_smoke_vseq::tmp_c {
  foreach (dut_cfg.range_base[i]) {
    dut_cfg.range_base[i]                   == 32'h7654_2500;
    dut_cfg.range_limit[i]                  == 32'h7654_2600;
    dut_cfg.range_perm[i].log_denied_access == 1;
    // dut_cfg.range_perm[i].execute_access    == 0;   // Note OK
    // dut_cfg.range_perm[i].write_access      == 1;   // Note OK
    // dut_cfg.range_perm[i].read_access       == 1;   // Note OK
    // dut_cfg.range_perm[i].enable            == 1;   // Note OK
  }
}

constraint ac_range_check_smoke_vseq::range_limit_c {
  solve dut_cfg.range_base before dut_cfg.range_limit;
  foreach (dut_cfg.range_limit[i]) {
    dut_cfg.range_limit[i] > dut_cfg.range_base[i];
  }
}

constraint ac_range_check_smoke_vseq::range_racl_policy_c {
  foreach (dut_cfg.range_racl_policy[i]) {
    soft dut_cfg.range_racl_policy[i].write_perm == 16'hFFFF;
    soft dut_cfg.range_racl_policy[i].read_perm  == 16'hFFFF;
  }
}

function ac_range_check_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task ac_range_check_smoke_vseq::body();
  tl_main_vars_t local_tl_main_vars;    // TODO used to force some values, find another better way

  // TODO, remove this chunk and make it random later
  local_tl_main_vars.rand_write = 1;
  local_tl_main_vars.write      = 1;
  local_tl_main_vars.rand_addr  = 0;
  local_tl_main_vars.addr       = 'h7654_24F0;
  local_tl_main_vars.rand_mask  = 0;
  local_tl_main_vars.mask       = 'hF;
  local_tl_main_vars.rand_data  = 0;
  local_tl_main_vars.data       = 'hABCD_0000;

  for (int i=1; i<=num_trans; i++) begin
    `uvm_info(`gfn, $sformatf("Starting seq %0d/%0d", i, num_trans), UVM_LOW)

    // TODO, remove this chunk and make it random later
    local_tl_main_vars.addr++;
    local_tl_main_vars.data++;

    `DV_CHECK_RANDOMIZE_FATAL(this)

    ac_range_check_init();
    send_single_tl_unfilt_tr(local_tl_main_vars);
    $display("\n");
  end
endtask : body
