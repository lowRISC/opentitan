// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ---------------------------------------------
// TileLink interface
// ---------------------------------------------
interface tl_if(input clk, input rst_n);

  wire tlul_pkg::tl_h2d_t h2d; // req
  wire tlul_pkg::tl_d2h_t d2h; // rsp

  tlul_pkg::tl_h2d_t h2d_int; // req (internal)
  tlul_pkg::tl_d2h_t d2h_int; // rsp (internal)

  dv_utils_pkg::if_mode_e if_mode; // interface mode - Host or Device

  modport dut_host_mp(output h2d_int, input d2h_int);
  modport dut_device_mp(input h2d_int, output d2h_int);

  clocking host_cb @(posedge clk);
    input  rst_n;
    output h2d_int;
    input  d2h;
  endclocking
  modport host_mp(clocking host_cb);

  clocking device_cb @(posedge clk);
    input  rst_n;
    input  h2d;
    output d2h_int;
  endclocking
  modport device_mp(clocking device_cb);

  clocking mon_cb @(posedge clk);
    input  rst_n;
    input  h2d;
    input  d2h;
  endclocking
  modport mon_mp(clocking mon_cb);

  assign h2d = (if_mode == dv_utils_pkg::Host) ? h2d_int : 'z;
  assign d2h = (if_mode == dv_utils_pkg::Device) ? d2h_int : 'z;

endinterface : tl_if
