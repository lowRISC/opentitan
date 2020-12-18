// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC Entropy Generation module

module kmac_entropy
  import kmac_pkg::*;
(
  input clk_i,
  input rst_ni,

  // EDN interface
  output edn_pkg::edn_req_t entropy_o,
  input  edn_pkg::edn_rsp_t entropy_i,

  // Entropy to internal
  output                        rand_valid_o,
  output [sha3_pkg::StateW-1:0] rand_data_o,
  input                         rand_consumed_i,

  // Status
  input in_progress_i,
  input in_keyblock_i,

  // Configurations
  //// Entropy refresh period in clk cycles
  input [31:0] refresh_period_i,

  //// SW update of seed
  input        seed_update_i,
  input [63:0] seed_data_i
);

  /////////////
  // Signals //
  /////////////

  // TODO: Implement logics
  logic unused_in_progress, unused_in_keyblock;
  assign unused_in_progress = in_progress_i;
  assign unused_in_keyblock = in_keyblock_i;

  logic [31:0] unused_refresh_period;
  assign unused_refresh_period = refresh_period_i;

  logic unused_seed_update;
  logic [63:0] unused_seed_data;
  assign unused_seed_update = seed_update_i;
  assign unused_seed_data = seed_data_i;

  assign rand_valid_o = 1'b 1;
  assign rand_data_o = '0;

  assign entropy_o = '{default: '0};

endmodule : kmac_entropy

