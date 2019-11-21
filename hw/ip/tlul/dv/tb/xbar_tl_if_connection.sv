// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Device TileLink interface connections
`CONNECT_TL_DEVICE_IF(rom)
`CONNECT_TL_DEVICE_IF(debug_mem)
`CONNECT_TL_DEVICE_IF(ram_main)
`CONNECT_TL_DEVICE_IF(eflash)
`CONNECT_TL_DEVICE_IF(uart)
`CONNECT_TL_DEVICE_IF(gpio)
`CONNECT_TL_DEVICE_IF(spi_device)
`CONNECT_TL_DEVICE_IF(flash_ctrl)
`CONNECT_TL_DEVICE_IF(rv_timer)
`CONNECT_TL_DEVICE_IF(hmac)
`CONNECT_TL_DEVICE_IF(aes)
`CONNECT_TL_DEVICE_IF(rv_plic)
`CONNECT_TL_DEVICE_IF(pinmux)

// Host TileLink interface connections
`CONNECT_TL_HOST_IF(corei)
`CONNECT_TL_HOST_IF(cored)
`CONNECT_TL_HOST_IF(dm_sba)
