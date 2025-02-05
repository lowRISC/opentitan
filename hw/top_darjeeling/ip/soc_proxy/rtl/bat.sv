// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module bat (
  // Input port
  input  tlul_pkg::tl_h2d_t tl_in_h2d_i,
  output tlul_pkg::tl_d2h_t tl_in_d2h_o,

  // Integrator bits used for custom BAT
  input logic [3:0]         integrator_id_i,

  // Translated output port
  output tlul_pkg::tl_h2d_t tl_out_h2d_o,
  input  tlul_pkg::tl_d2h_t tl_out_d2h_i
);

  // A valid request in the range [1G,2G) or a broadcast request is considered to be valid
  logic ctn_request;
  assign ctn_request = tl_in_h2d_i.a_valid & (tl_in_h2d_i.a_address[31:30] == 2'b01);

  logic [top_pkg::TL_AW-1:0] bat_address;
  logic [1:0] addr_msbs;
  assign addr_msbs = tl_in_h2d_i.a_address[31:30];

  // If there is a valid CTN request, perform the BAT (downlift to 0-1GB),
  // else use the original address
  assign bat_address = {ctn_request ? 2'b0 : addr_msbs, tl_in_h2d_i.a_address[29:0]};

  // Assemble the new TLUL request with the BAT'ed address
  tlul_pkg::tl_h2d_t tl_out_h2d_pre;
  assign tl_out_h2d_pre = '{
    a_valid:    tl_in_h2d_i.a_valid,
    a_opcode:   tl_in_h2d_i.a_opcode,
    a_size:     tl_in_h2d_i.a_size,
    a_source:   tl_in_h2d_i.a_source,
    a_address:  bat_address,
    a_mask:     tl_in_h2d_i.a_mask,
    a_user:     tl_in_h2d_i.a_user,
    a_data:     tl_in_h2d_i.a_data,
    a_param:    tl_in_h2d_i.a_param,
    d_ready:    tl_in_h2d_i.d_ready
  };

  // Regenerate integrity values after address change
  tlul_cmd_intg_gen u_cmd_intg_gen (
    .tl_i(tl_out_h2d_pre),
    .tl_o(tl_out_h2d_o)
  );

  // Feed back the response port
  assign tl_in_d2h_o = tl_out_d2h_i;

  // Integrator ID is unused in the open-source BAT
  logic unused_signals;
  assign unused_signals = ^integrator_id_i;
endmodule
