// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Device TileLink interface connections
`CONNECT_TL_DEVICE_IF(rom_tl_if,        rom,        TlRom)
`CONNECT_TL_DEVICE_IF(debug_mem_tl_if,  debug_mem,  TlDebugMem)
`CONNECT_TL_DEVICE_IF(ram_main_tl_if,   ram_main,   TlRamMain)
`CONNECT_TL_DEVICE_IF(eflash_tl_if,     eflash,     TlEflash)
`CONNECT_TL_DEVICE_IF(uart_tl_if,       uart,       TlUart)
`CONNECT_TL_DEVICE_IF(gpio_tl_if,       gpio,       TlGpio)
`CONNECT_TL_DEVICE_IF(spi_device_tl_if, spi_device, TlSpiDevice)
`CONNECT_TL_DEVICE_IF(flash_ctrl_tl_if, flash_ctrl, TlFlashCtrl)
`CONNECT_TL_DEVICE_IF(rv_timer_tl_if,   rv_timer,   TlRvTimer)
`CONNECT_TL_DEVICE_IF(hmac_tl_if,       hmac,       TlHmac)
`CONNECT_TL_DEVICE_IF(aes_tl_if,        aes,        TlAes)
`CONNECT_TL_DEVICE_IF(rv_plic_tl_if,    rv_plic,    TlRvPlic)
`CONNECT_TL_DEVICE_IF(pinmux_tl_if,     pinmux,     TlPinmux)

// Host TileLink interface connections
`CONNECT_TL_HOST_IF(corei_tl_if,  corei,  TlCorei)
`CONNECT_TL_HOST_IF(cored_tl_if,  cored,  TlCored)
`CONNECT_TL_HOST_IF(dm_sba_tl_if, dm_sba, TlDmSba)
