// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef DUT_HIER
  `define DUT_HIER            tb.dut
`endif
`define CHIP_HIER             `DUT_HIER.top_earlgrey

`define ALERT_HANDLER_HIER    `CHIP_HIER.u_alert_handler
`define CLKMGR_HIER           `CHIP_HIER.u_clkmgr_aon
`define CPU_HIER              `CHIP_HIER.u_rv_core_ibex
`define CPU_CORE_HIER         `CPU_HIER.u_core
`define CPU_TL_ADAPT_D_HIER   `CPU_HIER.tl_adapter_host_d_ibex
`define EFLASH_HIER           `CHIP_HIER.u_flash_ctrl.u_eflash.u_flash
`define GPIO_HIER             `CHIP_HIER.u_gpio
`define KEYMGR_HIER           `CHIP_HIER.u_keymgr
`define LC_CTRL_HIER          `CHIP_HIER.u_lc_ctrl
`define OTP_CTRL_HIER         `CHIP_HIER.u_otp_ctrl
`define RAM_MAIN_HIER         `CHIP_HIER.u_sram_ctrl_main.u_prim_ram_1p_scr
`define RAM_RET_HIER          `CHIP_HIER.u_sram_ctrl_ret_aon.u_prim_ram_1p_scr
`define ROM_CTRL_HIER         `CHIP_HIER.u_rom_ctrl
`define RSTMGR_HIER           `CHIP_HIER.u_rstmgr_aon
`define SPI_DEVICE_HIER       `CHIP_HIER.u_spi_device
`define UART_HIER             `CHIP_HIER.u_uart
`define USBDEV_HIER           `CHIP_HIER.u_usbdev
`define PWRMGR_HIER           `CHIP_HIER.u_pwrmgr_aon
`define OTBN_HIER             `CHIP_HIER.u_otbn

// The path to the actual memory array in rom_ctrl. This is a bit of a hack to allow a long path
// without overflowing 100 characters or including any whitespace (which breaks a DV_STRINGIFY call
// in the system-level testbench).
`ifdef DISABLE_ROM_INTEGRITY_CHECK
`define ROM_CTRL_INT_PATH     gen_rom_scramble_disabled.u_rom.u_prim_rom.`MEM_ARRAY_SUB
`else
`define ROM_CTRL_INT_PATH     gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom.`MEM_ARRAY_SUB
`endif

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
`define ICACHE_WAY0_HIER      `CPU_CORE_HIER.gen_rams.gen_rams_inner[0].gen_scramble_rams
`define ICACHE_WAY1_HIER      `CPU_CORE_HIER.gen_rams.gen_rams_inner[1].gen_scramble_rams
`define ICACHE0_TAG_MEM_HIER  `ICACHE_WAY0_HIER.tag_bank.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define ICACHE1_TAG_MEM_HIER  `ICACHE_WAY1_HIER.tag_bank.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define ICACHE0_DATA_MEM_HIER `ICACHE_WAY0_HIER.data_bank.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define ICACHE1_DATA_MEM_HIER `ICACHE_WAY1_HIER.data_bank.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define RAM_MAIN_MEM_HIER     `RAM_MAIN_HIER.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define RAM_RET_MEM_HIER      `RAM_RET_HIER.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define ROM_MEM_HIER          `ROM_CTRL_HIER.`ROM_CTRL_INT_PATH
`define OTP_GENERIC_HIER      `OTP_CTRL_HIER.u_otp.gen_generic.u_impl_generic
`define OTP_MEM_HIER          `OTP_GENERIC_HIER.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define OTBN_IMEM_HIER        `OTBN_HIER.u_imem.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define OTBN_DMEM_HIER        `OTBN_HIER.u_dmem.u_prim_ram_1p_adv.u_mem.`MEM_ARRAY_SUB
`define USBDEV_BUF_HIER       `USBDEV_HIER.gen_no_stubbed_memory.u_memory_2p.i_prim_ram_2p_async_adv.u_mem.`MEM_ARRAY_SUB
