// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Device TileLink interface connections
`CONNECT_TL_DEVICE_IF(rom_tl_if, dut.tl_rom_o, dut.tl_rom_i, TlRom)
`CONNECT_TL_DEVICE_IF(debug_mem_tl_if, dut.tl_debug_mem_o, dut.tl_debug_mem_i, TlDebugMem)
`CONNECT_TL_DEVICE_IF(ram_main_tl_if, dut.tl_ram_main_o, dut.tl_ram_main_i, TlRamMain)
`CONNECT_TL_DEVICE_IF(eflash_tl_if, dut.tl_eflash_o, dut.tl_eflash_i, TlEflash)
`CONNECT_TL_DEVICE_IF(uart_tl_if, dut.tl_uart_o, dut.tl_uart_i, TlUart)
`CONNECT_TL_DEVICE_IF(gpio_tl_if, dut.tl_gpio_o, dut.tl_gpio_i, TlGpio)
`CONNECT_TL_DEVICE_IF(spi_device_tl_if, dut.tl_spi_device_o, dut.tl_spi_device_i, TlSpiDevice)
`CONNECT_TL_DEVICE_IF(flash_ctrl_tl_if, dut.tl_flash_ctrl_o, dut.tl_flash_ctrl_i, TlFlashCtrl)
`CONNECT_TL_DEVICE_IF(rv_timer_tl_if, dut.tl_rv_timer_o, dut.tl_rv_timer_i, TlRvTimer)
`CONNECT_TL_DEVICE_IF(hmac_tl_if, dut.tl_hmac_o, dut.tl_hmac_i, TlHmac)
`CONNECT_TL_DEVICE_IF(rv_plic_tl_if, dut.tl_rv_plic_o, dut.tl_rv_plic_i, TlRvPlic)

// Host TileLink interface connections
`CONNECT_TL_HOST_IF(corei_tl_if, dut.tl_corei_i, dut.tl_corei_o, TlCorei)
`CONNECT_TL_HOST_IF(cored_tl_if, dut.tl_cored_i, dut.tl_cored_o, TlCored)
`CONNECT_TL_HOST_IF(dm_sba_tl_if, dut.tl_dm_sba_i, dut.tl_dm_sba_o, TlDmSba)
