// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define DUT_HIER        dut
`define CHIP_HIER       `DUT_HIER.top_earlgrey
`define UART_HIER       `CHIP_HIER.uart
`define GPIO_HIER       `CHIP_HIER.gpio
`define SPI_DEVICE_HIER `CHIP_HIER.spi_device
`define CPU_HIER        `CHIP_HIER.core
`define RAM_MAIN_HIER   `CHIP_HIER.u_ram1p_ram_main
`define ROM_HIER        `CHIP_HIER.u_rom_rom
`define FLASH_HIER      `CHIP_HIER.u_flash_eflash
`define FLASH0_MEM_HIER `FLASH_HIER.gen_flash_banks[0].u_flash.gen_flash.u_impl_generic.u_mem
`define FLASH1_MEM_HIER `FLASH_HIER.gen_flash_banks[1].u_flash.gen_flash.u_impl_generic.u_mem
