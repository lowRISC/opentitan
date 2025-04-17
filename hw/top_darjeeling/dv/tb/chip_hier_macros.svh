// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef DUT_HIER
  `define DUT_HIER            tb.dut
`endif
`define CHIP_HIER             `DUT_HIER.top_darjeeling

`define ALERT_HANDLER_HIER    `CHIP_HIER.u_alert_handler
`define CLKMGR_HIER           `CHIP_HIER.u_clkmgr_aon
`define CPU_HIER              `CHIP_HIER.u_rv_core_ibex
`define CPU_CORE_HIER         `CPU_HIER.u_core
`define CPU_TL_ADAPT_D_HIER   `CPU_HIER.tl_adapter_host_d_ibex
`define GPIO_HIER             `CHIP_HIER.u_gpio
`define KEYMGR_DPE_HIER       `CHIP_HIER.u_keymgr_dpe
`define LC_CTRL_HIER          `CHIP_HIER.u_lc_ctrl
`define OTP_CTRL_HIER         `CHIP_HIER.u_otp_ctrl
`define OTP_MACRO_HIER         `CHIP_HIER.u_otp_macro
`define RAM_MAIN_HIER         `CHIP_HIER.u_sram_ctrl_main.u_prim_ram_1p_scr
`define RAM_RET_HIER          `CHIP_HIER.u_sram_ctrl_ret_aon.u_prim_ram_1p_scr
`define RAM_MBOX_HIER         `CHIP_HIER.u_sram_ctrl_mbox.u_prim_ram_1p_scr
`define ROM_CTRL0_HIER        `CHIP_HIER.u_rom_ctrl0
`define ROM_CTRL1_HIER        `CHIP_HIER.u_rom_ctrl1
`define RSTMGR_HIER           `CHIP_HIER.u_rstmgr_aon
`define SPI_DEVICE_HIER       `CHIP_HIER.u_spi_device
`define UART_HIER             `CHIP_HIER.u_uart
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
`define ICACHE_WAY0_HIER      `CPU_CORE_HIER.gen_rams.gen_rams_inner[0].gen_scramble_rams
`define ICACHE_WAY1_HIER      `CPU_CORE_HIER.gen_rams.gen_rams_inner[1].gen_scramble_rams
`define ICACHE0_TAG_MEM_HIER  `ICACHE_WAY0_HIER.tag_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define ICACHE1_TAG_MEM_HIER  `ICACHE_WAY1_HIER.tag_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define ICACHE0_DATA_MEM_HIER `ICACHE_WAY0_HIER.data_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define ICACHE1_DATA_MEM_HIER `ICACHE_WAY1_HIER.data_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define RAM_MAIN_MEM_HIER     `RAM_MAIN_HIER.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define RAM_RET_MEM_HIER      `RAM_RET_HIER.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define RAM_MBOX_MEM_HIER     `RAM_MBOX_HIER.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define RAM_CTN_MEM_HIER      `DUT_HIER.u_prim_ram_1p_adv_ctn.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define ROM0_MEM_HIER         `ROM_CTRL0_HIER.`ROM_CTRL_INT_PATH
`define ROM1_MEM_HIER         `ROM_CTRL1_HIER.`ROM_CTRL_INT_PATH
`define SPI_DEVICE_EGRESS_HIER  `SPI_DEVICE_HIER.u_spid_dpram.gen_ram1r1w.u_sys2spi_mem.u_mem.`MEM_ARRAY_SUB
`define SPI_DEVICE_INGRESS_HIER `SPI_DEVICE_HIER.u_spid_dpram.gen_ram1r1w.u_spi2sys_mem.u_mem.`MEM_ARRAY_SUB
`define OTP_MEM_HIER          `OTP_MACRO_HIER.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define OTBN_IMEM_HIER        `OTBN_HIER.u_imem.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define OTBN_DMEM_HIER        `OTBN_HIER.u_dmem.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
