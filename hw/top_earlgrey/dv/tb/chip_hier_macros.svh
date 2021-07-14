// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define DUT_HIER              tb.dut
`define CHIP_HIER             `DUT_HIER.top_earlgrey

`define ALERT_HANDLER_HIER    `CHIP_HIER.u_alert_handler
`define CLKMGR_HIER           `CHIP_HIER.u_clkmgr_aon
`define CPU_HIER              `CHIP_HIER.u_rv_core_ibex
`define CPU_TL_ADAPT_D_HIER   `CPU_HIER.tl_adapter_host_d_ibex
`define EFLASH_HIER           `CHIP_HIER.u_flash_eflash.u_flash
`define GPIO_HIER             `CHIP_HIER.u_gpio
`define OTP_CTRL_HIER         `CHIP_HIER.u_otp_ctrl
`define RAM_MAIN_HIER         `CHIP_HIER.u_sram_ctrl_main.u_prim_ram_1p_scr
`define RAM_RET_HIER          `CHIP_HIER.u_sram_ctrl_ret_aon.u_prim_ram_1p_scr
`define ROM_CTRL_HIER         `CHIP_HIER.u_rom_ctrl
`define RSTMGR_HIER           `CHIP_HIER.u_rstmgr_aon
`define SPI_DEVICE_HIER       `CHIP_HIER.u_spi_device
`define UART_HIER             `CHIP_HIER.u_uart
`define USBDEV_HIER           `CHIP_HIER.u_usbdev

// Memory hierarchies.
// TODO: Temporarily only reference info type0 of the info partitions in flash. In the future, this
// needs to be upgraded to support all info types.
`define MEM_ARRAY_SUB         gen_generic.u_impl_generic.mem
`define EFLASH_GENERIC_HIER   `EFLASH_HIER.gen_generic.u_impl_generic
`define FLASH_BANK0_HIER      `EFLASH_GENERIC_HIER.gen_prim_flash_banks[0].u_prim_flash_bank
`define FLASH_BANK1_HIER      `EFLASH_GENERIC_HIER.gen_prim_flash_banks[1].u_prim_flash_bank
`define FLASH0_DATA_MEM_HIER  `FLASH_BANK0_HIER.u_mem.`MEM_ARRAY_SUB
`define FLASH0_INFO_MEM_HIER  `FLASH_BANK0_HIER.gen_info_types[0].u_info_mem.`MEM_ARRAY_SUB
`define FLASH1_DATA_MEM_HIER  `FLASH_BANK1_HIER.u_mem.`MEM_ARRAY_SUB
`define FLASH1_INFO_MEM_HIER  `FLASH_BANK1_HIER.gen_info_types[0].u_info_mem.`MEM_ARRAY_SUB
`define RAM_MAIN_MEM_HIER     `RAM_MAIN_HIER.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define RAM_RET_MEM_HIER      `RAM_RET_HIER.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define ROM_MEM_HIER          `ROM_CTRL_HIER.u_rom.u_rom.u_prim_rom.`MEM_ARRAY_SUB
`define OTP_GENERIC_HIER      `OTP_CTRL_HIER.u_otp.gen_generic.u_impl_generic
`define OTP_MEM_HIER          `OTP_GENERIC_HIER.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
