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
  typedef enum logic [5:0] {
      StIdle = 6'b011111,

      StActive = 6'b000100,

      StPhase1 = 6'b101101,

      StPhase2Cycle1 = 6'b000011,

      StPhase2Cycle2 = 6'b011000,

      StPhase2Cycle3 = 6'b101010,

      StError = 6'b110001,

      StTerminalError = 6'b110110
  } keccak_st_e;

  covergroup cmd_process_cg @(sw_cmd_process == 1);
    kmac_keccak_state: coverpoint keccak_st {
      bins active = {StActive, StPhase1, StPhase2Cycle1, StPhase2Cycle2, StPhase2Cycle3};
      bins inactive = {StIdle};
    }

    // TODO: check with designer, this might be unreachable.
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
