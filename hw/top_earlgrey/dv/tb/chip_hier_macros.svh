// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define DUT_HIER           dut
`define CHIP_HIER          `DUT_HIER.top_earlgrey
`define UART_HIER          `CHIP_HIER.u_uart
`define GPIO_HIER          `CHIP_HIER.u_gpio
`define SPI_DEVICE_HIER    `CHIP_HIER.u_spi_device
`define ALERT_HANDLER_HIER `CHIP_HIER.u_alert_handler
`define CPU_HIER           `CHIP_HIER.u_rv_core_ibex
`define RAM_MAIN_HIER      `CHIP_HIER.u_ram1p_ram_main.u_prim_ram_1p_adv.u_mem
`define RAM_RET_HIER       `CHIP_HIER.u_ram1p_ram_ret_aon.u_prim_ram_1p_adv.u_mem
`define ROM_HIER           `CHIP_HIER.u_rom_rom.u_prim_rom
`define FLASH_HIER         `CHIP_HIER.u_flash_eflash.u_flash
`define RSTMGR_HIER        `CHIP_HIER.u_rstmgr_aon
`define CLKMGR_HIER        `CHIP_HIER.u_clkmgr_aon
`define USBDEV_HIER        `CHIP_HIER.u_usbdev
`define FLASH_BANK0        `FLASH_HIER.gen_generic.u_impl_generic.gen_prim_flash_banks[0].u_prim_flash_bank
`define FLASH_BANK1        `FLASH_HIER.gen_generic.u_impl_generic.gen_prim_flash_banks[1].u_prim_flash_bank
`define FLASH0_MEM_HIER    `FLASH_BANK0.u_mem
`define FLASH1_MEM_HIER    `FLASH_BANK1.u_mem
// TODO: Temporarily only reference info type0 of the info partitions
// in the future, this needs to be upgraded to support all info types
`define FLASH0_INFO_HIER   `FLASH_BANK0.gen_info_types[0].u_info_mem
`define FLASH1_INFO_HIER   `FLASH_BANK1.gen_info_types[0].u_info_mem
`define OTP_MEM_HIER       `CHIP_HIER.u_otp_ctrl.u_otp.gen_generic.u_impl_generic.u_prim_ram_1p_adv.\
                           u_mem.gen_generic.u_impl_generic
