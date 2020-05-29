// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink interface connection macros
// ---------------------------------------------

// reset is from tb.clk_rst_if, disable driving reset in this clk_rst_if
`define DRIVE_CLK(name, freq = $urandom_range(10, 100)) \
  wire ``name``; \
  clk_rst_if clk_rst_if_``name``(.clk(``name``), .rst_n(rst_n)); \
  initial begin \
    clk_rst_if_``name``.set_active(.drive_rst_n_val(0)); \
    clk_rst_if_``name``.set_freq_mhz(freq); \
  end

`define DRIVE_TL_DEVICE_IF(tl_name, path = dut, clk, rst_n, i_sfx = i, o_sfx = o) \
     force ``tl_name``_tl_if.h2d = ``path``.tl_``tl_name``_``o_sfx``; \
     force ``path``.tl_``tl_name``_``i_sfx`` = ``tl_name``_tl_if.d2h; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if);

`define DRIVE_TL_HOST_IF(tl_name, path = dut, clk, rst_n, i_sfx = i, o_sfx = o) \
     force ``tl_name``_tl_if.d2h = ``path``.tl_``tl_name``_``o_sfx``; \
     force ``path``.tl_``tl_name``_``i_sfx`` = ``tl_name``_tl_if.h2d; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if);

`define CONNECT_TL_DEVICE_IF(tl_name, path = dut, clk, rst_n, i_sfx = i, o_sfx = o) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     `DRIVE_TL_DEVICE_IF(tl_name, path, clk, rst_n, i_sfx, o_sfx) \
   end

`define CONNECT_TL_HOST_IF(tl_name, path = dut, clk, rst_n, i_sfx = i, o_sfx = o) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     `DRIVE_TL_HOST_IF(tl_name, path, clk, rst_n, i_sfx, o_sfx) \
   end

`define CONNECT_TL_MON_IF(dut_h2d, dut_d2h, tl_name, clk, rst_n) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     force ``tl_name``_tl_if.h2d = dut_h2d; \
     force ``tl_name``_tl_if.d2h = dut_d2h; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if); \
   end

