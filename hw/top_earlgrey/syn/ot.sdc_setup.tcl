# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generic parameters for sdc file

set CLK_PERIOD_FACTOR 0.95
set MAIN_TCK_FACTOR   0.85
set MAIN_CLK_PIN u_ast/clk_src_sys_o
set USB_CLK_PIN  u_ast/clk_src_usb_o
set IO_CLK_PIN   u_ast/clk_src_io_o
set CLK_PIN      clk_o
set CLK_DST_PIN  clk_o
set AON_CLK_PIN  u_ast/clk_src_aon_o
