// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_base_vseq extends cip_base_vseq #(
    .RAL_T               (ac_range_check_reg_block),
    .CFG_T               (ac_range_check_env_cfg),
    .COV_T               (ac_range_check_env_cov),
    .VIRTUAL_SEQUENCER_T (ac_range_check_virtual_sequencer)
  );
  `uvm_object_utils(ac_range_check_base_vseq)

  // Various knobs to enable certain routines
  bit do_ac_range_check_init = 1'b1;

  // Randomized variables
  rand bit [TL_DW-3:0] range_base[NUM_RANGES];  // Granularity is 32-bit words
  rand bit [TL_DW-3:0] range_limit[NUM_RANGES]; // Granularity is 32-bit words
  rand range_perm_t    range_perm[NUM_RANGES];
  rand racl_policy_t   range_racl_policy[NUM_RANGES];

  // Constraints
  extern constraint range_limit_c;
  extern constraint range_racl_policy_c;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern task dut_init(string reset_kind = "HARD");
  extern task ac_range_check_init();
  extern task cfg_range_base();
  extern task cfg_range_limit();
  extern task cfg_range_perm();
  extern task cfg_range_racl_policy();
endclass : ac_range_check_base_vseq


constraint ac_range_check_base_vseq::range_limit_c {
  solve range_base before range_limit;
  foreach (range_limit[i]) {
    range_limit[i] > range_base[i];
  }
}

constraint ac_range_check_base_vseq::range_racl_policy_c {
  foreach (range_racl_policy[i]) {
    soft range_racl_policy[i].write_perm == 16'hFFFF;
    soft range_racl_policy[i].read_perm  == 16'hFFFF;
  }
}

function ac_range_check_base_vseq::new(string name="");
  super.new(name);
endfunction : new

task ac_range_check_base_vseq::dut_init(string reset_kind = "HARD");
  super.dut_init();
  if (do_ac_range_check_init) begin
    ac_range_check_init();
  end
endtask : dut_init

task ac_range_check_base_vseq::ac_range_check_init();
  cfg_range_base();
  cfg_range_limit();
  cfg_range_perm();
  cfg_range_racl_policy();
endtask : ac_range_check_init

task ac_range_check_base_vseq::cfg_range_base();
  foreach (range_base[i]) begin
    ral.range_base[i].set({range_base[i], 2'b00});
    csr_update(.csr(ral.range_base[i]));
  end
endtask : cfg_range_base

task ac_range_check_base_vseq::cfg_range_limit();
  foreach (range_limit[i]) begin
    ral.range_limit[i].set({range_limit[i], 2'b00});
    csr_update(.csr(ral.range_limit[i]));
  end
endtask : cfg_range_limit

task ac_range_check_base_vseq::cfg_range_perm();
  foreach (range_perm[i]) begin
    ral.range_perm[i].set({
      prim_mubi_pkg::mubi4_bool_to_mubi(range_perm[i].log_denied_access),
      prim_mubi_pkg::mubi4_bool_to_mubi(range_perm[i].execute_access   ),
      prim_mubi_pkg::mubi4_bool_to_mubi(range_perm[i].write_access     ),
      prim_mubi_pkg::mubi4_bool_to_mubi(range_perm[i].read_access      ),
      prim_mubi_pkg::mubi4_bool_to_mubi(range_perm[i].enable           )
    });
    csr_update(.csr(ral.range_perm[i]));
  end
endtask : cfg_range_perm

task ac_range_check_base_vseq::cfg_range_racl_policy();
  foreach (range_racl_policy[i]) begin
    ral.range_racl_policy_shadowed[i].set(range_racl_policy[i]);
    // Shodowed register: the 2 writes are automatcally managed by the csr_utils_pkg
    csr_update(.csr(ral.range_racl_policy_shadowed[i]));
  end
endtask : cfg_range_racl_policy
