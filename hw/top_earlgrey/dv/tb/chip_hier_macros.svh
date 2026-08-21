// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef DUT_HIER
  `define DUT_HIER            tb.dut
`endif
`define PD_MAIN_HIER          `DUT_HIER.top_earlgrey.earlgrey_pd_main
`define PD_AON_HIER           `DUT_HIER.top_earlgrey.earlgrey_pd_aon

`define ALERT_HANDLER_HIER    `PD_MAIN_HIER.u_alert_handler
`define CLKMGR_HIER           `PD_AON_HIER.u_clkmgr
`define CPU_HIER              `PD_MAIN_HIER.u_rv_core_ibex
`define CPU_CORE_HIER         `CPU_HIER.u_core
`define CPU_TL_ADAPT_D_HIER   `CPU_HIER.tl_adapter_host_d_ibex
`define RRAM_MACRO_HIER       `PD_MAIN_HIER.u_rram_macro
`define GPIO_HIER             `PD_MAIN_HIER.u_gpio
`define KEYMGR_DPE_HIER       `PD_MAIN_HIER.u_keymgr_dpe
`define LC_CTRL_HIER          `PD_MAIN_HIER.u_lc_ctrl
`define OTP_CTRL_HIER         `PD_MAIN_HIER.u_otp_ctrl
`define RAM_MAIN_HIER         `PD_MAIN_HIER.u_sram_ctrl_main.u_prim_ram_1p_scr
`define RAM_RET_HIER          `PD_AON_HIER.u_sram_ctrl_ret.u_prim_ram_1p_scr
`define ROM_CTRL_HIER         `PD_MAIN_HIER.u_rom_ctrl
`define RSTMGR_HIER           `PD_AON_HIER.u_rstmgr
`define SPI_DEVICE_HIER       `PD_MAIN_HIER.u_spi_device
`define UART_HIER             `PD_MAIN_HIER.u_uart
`define USBDEV_HIER           `PD_MAIN_HIER.u_usbdev
`define PWRMGR_HIER           `PD_AON_HIER.u_pwrmgr
`define OTBN_HIER             `PD_MAIN_HIER.u_otbn

// The path to the actual memory array in rom_ctrl. This is a bit of a hack to allow a long path
// without overflowing 100 characters or including any whitespace (which breaks a DV_STRINGIFY call
// in the system-level testbench).
`ifdef DISABLE_ROM_INTEGRITY_CHECK
`define ROM_CTRL_INT_PATH     gen_rom_scramble_disabled.u_rom.u_prim_rom.`MEM_ARRAY_SUB
`else
`define ROM_CTRL_INT_PATH     gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom.`MEM_ARRAY_SUB
`endif

// Memory hierarchies.
`define MEM_ARRAY_SUB         mem
// Defines `RRAM_DATA_MEM_PATH`/`RRAM_INFO_MEM_PATH`, resolved to whichever rram_ctrl_bkdr_util
// implementation (open-source or vendor) is mapped in for this build.
`include "rram_ctrl_bkdr_util_hier.svh"
`define RRAM_DATA_MEM_HIER    `RRAM_MACRO_HIER.`RRAM_DATA_MEM_PATH
`define RRAM_INFO_MEM_HIER    `RRAM_MACRO_HIER.`RRAM_INFO_MEM_PATH
`define ICACHE_WAY0_HIER      `CPU_CORE_HIER.gen_rams.gen_rams_inner[0].gen_scramble_rams
`define ICACHE_WAY1_HIER      `CPU_CORE_HIER.gen_rams.gen_rams_inner[1].gen_scramble_rams
`define ICACHE0_TAG_MEM_HIER  `ICACHE_WAY0_HIER.tag_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define ICACHE1_TAG_MEM_HIER  `ICACHE_WAY1_HIER.tag_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define ICACHE0_DATA_MEM_HIER `ICACHE_WAY0_HIER.data_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define ICACHE1_DATA_MEM_HIER `ICACHE_WAY1_HIER.data_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define RAM_MAIN_MEM_HIER     `RAM_MAIN_HIER.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define RAM_RET_MEM_HIER      `RAM_RET_HIER.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define ROM_MEM_HIER          `ROM_CTRL_HIER.`ROM_CTRL_INT_PATH
`define OTBN_IMEM_HIER        `OTBN_HIER.u_imem.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define OTBN_DMEM_HIER        `OTBN_HIER.u_dmem.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
`define USBDEV_BUF_HIER       `USBDEV_HIER.gen_no_stubbed_memory.u_memory_1p.gen_ram_inst[0].u_mem.`MEM_ARRAY_SUB
