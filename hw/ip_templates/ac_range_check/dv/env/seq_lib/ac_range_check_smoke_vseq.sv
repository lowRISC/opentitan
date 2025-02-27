// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_smoke_vseq extends ac_range_check_base_vseq;
  `uvm_object_utils(ac_range_check_smoke_vseq)

  // Constraints
  // extern constraint range_limit_c;
  extern constraint range_racl_policy_c;
  extern constraint tmp_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : ac_range_check_smoke_vseq

// TODO remove this temporary directed constraint
constraint ac_range_check_smoke_vseq::tmp_c {
  foreach (range_base[i]) {
    range_base[i]                   == 32'h7654_2500;
    range_limit[i]                  == 32'h7654_2600;
    range_perm[i].log_denied_access == 1;
    range_perm[i].execute_access    == 1;
    range_perm[i].write_access      == 1;
    range_perm[i].read_access       == 1;
    range_perm[i].enable            == 1;
  }
}

// TODO uncomment that constraint
// constraint ac_range_check_smoke_vseq::range_limit_c {
//   solve range_base before range_limit;
//   foreach (range_limit[i]) {
//     range_limit[i] > range_base[i];
//   }
// }

constraint ac_range_check_smoke_vseq::range_racl_policy_c {
  foreach (range_racl_policy[i]) {
    soft range_racl_policy[i].write_perm == 16'hFFFF;
    soft range_racl_policy[i].read_perm  == 16'hFFFF;
  }
}

function ac_range_check_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task ac_range_check_smoke_vseq::body();
  // TODO, remove this chunk and make it random later
  tl_main_vars.rand_write = 0;
  tl_main_vars.write      = 0;
  tl_main_vars.rand_addr  = 0;
  tl_main_vars.addr       = 'h7654_24FF;
  tl_main_vars.rand_mask  = 0;
  tl_main_vars.mask       = 'hF;
  tl_main_vars.rand_data  = 0;
  tl_main_vars.data       = 'hABCD_FE97;

  // Out of range address
  send_single_tl_unfilt_tr(tl_main_vars);

  // In range address
  tl_main_vars.addr       = 'h7654_25F1;
  send_single_tl_unfilt_tr(tl_main_vars);
  tl_main_vars.addr       = 'h7654_2500;
  send_single_tl_unfilt_tr(tl_main_vars);
endtask : body
