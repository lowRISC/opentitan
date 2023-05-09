// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface kmac_cov_if
  (
   input logic     sw_cmd_process,
   input bit [5:0] keccak_st,
   input bit [3:0] msgfifo_depth,
   input bit       msgfifo_full,
   input bit       msgfifo_empty
   );

  `include "dv_fcov_macros.svh"

  import sha3_pkg::*;

  covergroup cmd_process_cg @(sw_cmd_process == 1);
    kmac_keccak_state: coverpoint keccak_st {
      bins active = {KeccakStActive, KeccakStPhase1, KeccakStPhase2Cycle1, KeccakStPhase2Cycle2,
                     KeccakStPhase2Cycle3};
      bins inactive = {KeccakStIdle};
    }

    kmac_msgfifo_full: coverpoint msgfifo_full {
      bins full     = {1};
      bins not_full = {0};
    }

    kmac_msgfifo_empty: coverpoint msgfifo_empty {
      bins empty     = {1};
      bins not_empty = {0};
    }

    kmac_msgfifo_has_data: coverpoint msgfifo_depth {
      bins has_data = {[1:15]};
    }
  endgroup

  `DV_FCOV_INSTANTIATE_CG(cmd_process_cg)
endinterface
