// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Device TileLink interface connections
`CONNECT_TL_DEVICE_IF(sram_tl_if, dut.tl_d_o[tl_main_pkg::TlSram],
                      dut.tl_d_i[tl_main_pkg::TlSram], TlSram)
`CONNECT_TL_DEVICE_IF(uart_tl_if, dut.tl_d_o[tl_main_pkg::TlUart],
                      dut.tl_d_i[tl_main_pkg::TlUart], TlUart)
`CONNECT_TL_DEVICE_IF(Gpio_tl_if, dut.tl_d_o[tl_main_pkg::TlGpio],
                      dut.tl_d_i[tl_main_pkg::TlGpio], TlGpio)

// Host TileLink interface connections
`CONNECT_TL_HOST_IF(corei_tl_if, dut.tl_h_i[tl_main_pkg::TlCoreI],
                      dut.tl_h_o[tl_main_pkg::TlCoreI], TlCoreI)
`CONNECT_TL_HOST_IF(cored_tl_if, dut.tl_h_i[tl_main_pkg::TlCoreD],
                      dut.tl_h_o[tl_main_pkg::TlCoreD], TlCoreD)
`CONNECT_TL_HOST_IF(debug_tl_if, dut.tl_h_i[tl_main_pkg::TlDebugSba],
                      dut.tl_h_o[tl_main_pkg::TlDebugSba], TlDebugSba)
