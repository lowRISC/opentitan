// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ---------------------------------------------
// TileLink interface
// ---------------------------------------------
interface tl_if(input clk, input rst_n);

  wire tlul_pkg::tl_h2d_t h2d; // req
  wire tlul_pkg::tl_d2h_t d2h; // rsp
  modport dut_host_mp(output h2d, input d2h);
  modport dut_device_mp(input h2d, output d2h);

  clocking host_cb @(posedge clk);
    input  rst_n;
    output h2d;
    input  d2h;
  endclocking
  modport host_mp(clocking host_cb);

  clocking device_cb @(posedge clk);
    input  rst_n;
    input  h2d;
    output d2h;
  endclocking
  modport device_mp(clocking device_cb);

  clocking mon_cb @(posedge clk);
    input  rst_n;
    input  h2d;
    input  d2h;
  endclocking
  modport mon_mp(clocking mon_cb);

endinterface : tl_if
