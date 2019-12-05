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
     force ``path``.tlul_assert_device_``tl_name``.tlul_assert_ctrl = tlul_assert_ctrl; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"tl_name`"), "vif", \
                                        ``tl_name``_tl_if); \
   end

`define CONNECT_TL_HOST_IF(tl_name, path = dut) \
   tl_if ``tl_name``_tl_if(clk, rst_n); \
   initial begin \
     force ``tl_name``_tl_if.d2h = ``path``.tl_``tl_name``_o; \
     force ``path``.tl_``tl_name``_i = ``tl_name``_tl_if.h2d; \
     force ``path``.tlul_assert_host_``tl_name``.tlul_assert_ctrl = tlul_assert_ctrl; \
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

