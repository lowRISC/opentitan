// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A very simple (unclocked) interface for sampling the racl_policies_o output

interface racl_ctrl_policies_if ();
  logic [$bits(top_racl_pkg::racl_policy_vec_t)-1:0] policies;

  function automatic top_racl_pkg::racl_policy_t get_policy(int unsigned idx);
    int unsigned msb = (idx + 1) * $bits(top_racl_pkg::racl_policy_t) - 1;
    return policies[msb -: $bits(top_racl_pkg::racl_policy_t)];
  endfunction
endinterface
