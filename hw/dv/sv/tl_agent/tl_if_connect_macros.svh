// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink interface connection macros
// ---------------------------------------------

`define CONNECT_TL_DEVICE_IF(intf_inst, dut_h2d, dut_d2h, intf_name) \
   tl_if intf_inst(clk, rst_n); \
   initial begin \
     force intf_inst.h2d = dut_h2d; \
     force dut_d2h = intf_inst.d2h; \
     uvm_config_db#(virtual tl_if)::set(null, $sformatf("*%0s*", `"intf_name`"), "vif", \
                                        intf_inst); \
   end

`define CONNECT_TL_HOST_IF(intf_inst, dut_h2d, dut_d2h, intf_name) \
   tl_if intf_inst(clk, rst_n); \
   initial begin \
     force intf_inst.d2h = dut_d2h; \
     force dut_h2d = intf_inst.h2d; \
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
