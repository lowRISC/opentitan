// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink interface connection macros
// ---------------------------------------------

// TODO, use random clock frequency for now , need to get frequency from hjson
// reset is from tb.clk_rst_if, disable driving reset in this clk_rst_if
`define CONNECT_CLK(name) \
  wire ``name``; \
  clk_rst_if clk_rst_if_``name``(.clk(``name``), .rst_n(rst_n)); \
  initial begin \
    clk_rst_if_``name``.set_active(.drive_rst_n_val(0)); \
    clk_rst_if_``name``.set_freq_mhz($urandom_range(10, 100)); \
  end

// TODO, all resets tie together
`define CONNECT_RST(name) \
  wire ``name`` = rst_n;


`define CONNECT_TL_DEVICE_IF(tl_name, path = dut, clk, rst_n) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     force ``tl_name``_tl_if.h2d = ``path``.tl_``tl_name``_o; \
     force ``path``.tl_``tl_name``_i = ``tl_name``_tl_if.d2h; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if); \
   end

`define CONNECT_TL_HOST_IF(tl_name, path = dut, clk, rst_n) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     force ``tl_name``_tl_if.d2h = ``path``.tl_``tl_name``_o; \
     force ``path``.tl_``tl_name``_i = ``tl_name``_tl_if.h2d; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if); \
   end

`define CONNECT_TL_MON_IF(dut_h2d, dut_d2h, tl_name, clk, rst_n) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     force ``tl_name``_tl_if.h2d = dut_h2d; \
     force ``tl_name``_tl_if.d2h = dut_d2h; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if); \
   end

