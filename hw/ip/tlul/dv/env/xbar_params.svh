// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// Num of valid host source id bits, the upper bits should be tied to zero
parameter int VALID_HOST_ID_WIDTH = 6;

// List of Xbar device memory map
tl_device_t xbar_devices[$] = '{
    '{"TlRom",       ADDR_SPACE_ROM       , ADDR_SPACE_ROM        | ADDR_MASK_ROM       },
    '{"TlDebugMem",  ADDR_SPACE_DEBUG_MEM , ADDR_SPACE_DEBUG_MEM  | ADDR_MASK_DEBUG_MEM },
    '{"TlRamMain",   ADDR_SPACE_RAM_MAIN  , ADDR_SPACE_RAM_MAIN   | ADDR_MASK_RAM_MAIN  },
    '{"TlEflash",    ADDR_SPACE_EFLASH    , ADDR_SPACE_EFLASH     | ADDR_MASK_EFLASH    },
    '{"TlUart",      ADDR_SPACE_UART      , ADDR_SPACE_UART       | ADDR_MASK_UART      },
    '{"TlGpio",      ADDR_SPACE_GPIO      , ADDR_SPACE_GPIO       | ADDR_MASK_GPIO      },
    '{"TlSpiDevice", ADDR_SPACE_SPI_DEVICE, ADDR_SPACE_SPI_DEVICE | ADDR_MASK_SPI_DEVICE},
    '{"TlFlashCtrl", ADDR_SPACE_FLASH_CTRL, ADDR_SPACE_FLASH_CTRL | ADDR_MASK_FLASH_CTRL},
    '{"TlRvTimer",   ADDR_SPACE_RV_TIMER  , ADDR_SPACE_RV_TIMER   | ADDR_MASK_RV_TIMER  },
    '{"TlHmac",      ADDR_SPACE_HMAC      , ADDR_SPACE_HMAC       | ADDR_MASK_HMAC      },
    '{"TlAes",       ADDR_SPACE_AES      , ADDR_SPACE_AES         | ADDR_MASK_AES       },
    '{"TlRvPlic",    ADDR_SPACE_RV_PLIC   , ADDR_SPACE_RV_PLIC    | ADDR_MASK_RV_PLIC   }};

// List of Xbar hosts
tl_host_t xbar_hosts[$] = '{
    '{"TlCorei", 0, '{"TlRom", "TlDebugMem", "TlRamMain", "TlEflash"}},
    '{"TlCored", 1, '{"TlRom", "TlDebugMem", "TlRamMain", "TlEflash", "TlUart", "TlGpio",
                       "TlSpiDevice", "TlFlashCtrl", "TlRvTimer", "TlHmac", "TlAes", "TlRvPlic"}},
    '{"TlDmSba", 2, '{"TlRom", "TlRamMain", "TlEflash", "TlUart", "TlGpio",
                      "TlSpiDevice", "TlFlashCtrl", "TlRvTimer", "TlHmac", "TlAes", "TlRvPlic"}}};
