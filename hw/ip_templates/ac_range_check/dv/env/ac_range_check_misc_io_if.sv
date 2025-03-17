// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to handle signal level code for the miscellaneous signals without an attached
// UVM agent
interface ac_range_check_misc_io_if();
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import ac_range_check_env_pkg::*;
  import ac_range_check_test_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Imports from packages
  import prim_mubi_pkg::mubi8_t;
  import prim_mubi_pkg::MuBi8False;
  import prim_mubi_pkg::MuBi8True;
  import prim_mubi_pkg::mubi8_bool_to_mubi;
  import top_racl_pkg::NrRaclPolicies;
  import top_racl_pkg::RACL_POLICY_VEC_DEFAULT;
  import top_racl_pkg::racl_policy_vec_t;

  // Variables corresponding to some of the DUT signals
  mubi8_t           range_check_overwrite;
  racl_policy_vec_t racl_policies;
  logic             racl_error;

  // Methods to manage range_check_overwrite
  function automatic void set_range_check_overwrite(bit val);
    range_check_overwrite = mubi8_bool_to_mubi(val);
  endfunction : set_range_check_overwrite

  // Methods to manage racl_policies
  function automatic void init_racl_policies();
    racl_policies = RACL_POLICY_VEC_DEFAULT;
  endfunction : init_racl_policies

  function automatic void set_racl_policies(int unsigned idx, racl_policy_t perm);
    if (idx >= NrRaclPolicies) begin
      `uvm_fatal("ac_range_check_misc_io_if", $sformatf("Invalid RACL policy index %0d", idx))
    end
    racl_policies[idx] = perm;
  endfunction : set_racl_policies

  function automatic racl_policy_t get_racl_policies(int unsigned idx);
    if (idx >= NrRaclPolicies) begin
      `uvm_fatal("ac_range_check_misc_io_if", $sformatf("Invalid RACL policy index %0d", idx))
    end
    return racl_policies[idx];
  endfunction : get_racl_policies

endinterface : ac_range_check_misc_io_if
