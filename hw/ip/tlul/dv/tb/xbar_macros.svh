// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink interface connection macros
// ---------------------------------------------

`define CONNECT_TL_DEVICE_IF(intf_inst, tl_name, intf_name) \
   tl_if intf_inst(clk, rst_n); \
   initial begin \
     force intf_inst.h2d = dut.tl_``tl_name``_o; \
     force dut.tl_``tl_name``_i = intf_inst.d2h; \
     force dut.tlul_assert_``tl_name``.tlul_assert_ctrl = tlul_assert_ctrl; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"intf_name`"), "vif", \
                                        intf_inst); \
   end

`define CONNECT_TL_HOST_IF(intf_inst, tl_name, intf_name) \
   tl_if intf_inst(clk, rst_n); \
   initial begin \
     force intf_inst.d2h = dut.tl_``tl_name``_o; \
     force dut.tl_``tl_name``_i = intf_inst.h2d; \
     force dut.tlul_assert_``tl_name``.tlul_assert_ctrl = tlul_assert_ctrl; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"intf_name`"), "vif", \
                                        intf_inst); \
   end

`define CONNECT_TL_MON_IF(intf_inst, dut_h2d, dut_d2h, intf_name) \
   tl_if intf_inst(clk, rst_n); \
   initial begin \
     force intf_inst.h2d = dut_h2d; \
     force intf_inst.d2h = dut_d2h; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"intf_name`"), "vif", \
                                        intf_inst); \
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

