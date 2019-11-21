// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink interface connection macros
// ---------------------------------------------

`define CONNECT_TL_DEVICE_IF(tl_name, path = dut) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     force ``tl_name``_tl_if.h2d = ``path``.tl_``tl_name``_o; \
     force ``path``.tl_``tl_name``_i = ``tl_name``_tl_if.d2h; \
     force ``path``.tlul_assert_``tl_name``.tlul_assert_ctrl = tlul_assert_ctrl; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if); \
   end

`define CONNECT_TL_HOST_IF(tl_name, path = dut) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     force ``tl_name``_tl_if.d2h = ``path``.tl_``tl_name``_o; \
     force ``path``.tl_``tl_name``_i = ``tl_name``_tl_if.h2d; \
     force ``path``.tlul_assert_``tl_name``.tlul_assert_ctrl = tlul_assert_ctrl; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if); \
   end

`define CONNECT_TL_MON_IF(dut_h2d, dut_d2h, tl_name) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     force ``tl_name``_tl_if.h2d = dut_h2d; \
     force ``tl_name``_tl_if.d2h = dut_d2h; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if); \
   end

 `define BIND_ASSERT_TL_DEVICE(tl_name) \
  bind xbar_main tlul_assert #( \
    .EndpointType("Host") \
  ) tlul_assert_``tl_name`` ( \
    .clk_i (clk_main_i), \
    .rst_ni(rst_main_ni), \
    .h2d   (tl_``tl_name``_o), \
    .d2h   (tl_``tl_name``_i) \
  );

`define BIND_ASSERT_TL_HOST(tl_name) \
  bind xbar_main tlul_assert #( \
    .EndpointType("Device") \
  ) tlul_assert_``tl_name`` ( \
    .clk_i (clk_main_i), \
    .rst_ni(rst_main_ni), \
    .h2d   (tl_``tl_name``_i), \
    .d2h   (tl_``tl_name``_o) \
  );

