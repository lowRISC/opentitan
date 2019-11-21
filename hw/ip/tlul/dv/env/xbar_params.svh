// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// List of Xbar device memory map
tl_device_t xbar_devices[$] = '{
    '{"rom",        ADDR_SPACE_ROM       , ADDR_SPACE_ROM        | ADDR_MASK_ROM       },
    '{"debug_mem",  ADDR_SPACE_DEBUG_MEM , ADDR_SPACE_DEBUG_MEM  | ADDR_MASK_DEBUG_MEM },
    '{"ram_main",   ADDR_SPACE_RAM_MAIN  , ADDR_SPACE_RAM_MAIN   | ADDR_MASK_RAM_MAIN  },
    '{"eflash",     ADDR_SPACE_EFLASH    , ADDR_SPACE_EFLASH     | ADDR_MASK_EFLASH    },
    '{"uart",       ADDR_SPACE_UART      , ADDR_SPACE_UART       | ADDR_MASK_UART      },
    '{"gpio",       ADDR_SPACE_GPIO      , ADDR_SPACE_GPIO       | ADDR_MASK_GPIO      },
    '{"spi_device", ADDR_SPACE_SPI_DEVICE, ADDR_SPACE_SPI_DEVICE | ADDR_MASK_SPI_DEVICE},
    '{"flash_ctrl", ADDR_SPACE_FLASH_CTRL, ADDR_SPACE_FLASH_CTRL | ADDR_MASK_FLASH_CTRL},
    '{"rv_timer",   ADDR_SPACE_RV_TIMER  , ADDR_SPACE_RV_TIMER   | ADDR_MASK_RV_TIMER  },
    '{"hmac",       ADDR_SPACE_HMAC      , ADDR_SPACE_HMAC       | ADDR_MASK_HMAC      },
    '{"aes",        ADDR_SPACE_AES       , ADDR_SPACE_AES        | ADDR_MASK_AES       },
    '{"rv_plic",    ADDR_SPACE_RV_PLIC   , ADDR_SPACE_RV_PLIC    | ADDR_MASK_RV_PLIC   },
    '{"pinmux",     ADDR_SPACE_PINMUX    , ADDR_SPACE_PINMUX     | ADDR_MASK_PINMUX   }};

// List of Xbar hosts
tl_host_t xbar_hosts[$] = '{
    '{"corei", 0, '{"rom", "debug_mem", "ram_main", "eflash"}},
    '{"cored", 1, '{"rom", "debug_mem", "ram_main", "eflash", "uart", "gpio", "spi_device",
                    "flash_ctrl", "rv_timer", "hmac", "aes", "rv_plic", "pinmux"}},
    '{"dm_sba", 2, '{"rom", "ram_main", "eflash", "uart", "gpio", "spi_device",
                     "flash_ctrl", "rv_timer", "hmac", "aes", "rv_plic", "pinmux"}}};
