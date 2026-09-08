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

// The path to the prim_rom instance in rom_ctrl. This is a bit of a hack to allow a long path
// without overflowing 100 characters or including any whitespace (which breaks a DV_STRINGIFY call
// in the system-level testbench).
`ifdef DISABLE_ROM_INTEGRITY_CHECK
`define ROM_CTRL_INT_PATH     gen_rom_scramble_disabled.u_rom.u_prim_rom
`else
`define ROM_CTRL_INT_PATH     gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom
`endif

// Memory hierarchies.
// Defines `RRAM_DATA_MEM_PATH`/`RRAM_INFO_MEM_PATH`, resolved to whichever rram_ctrl_bkdr_util
// implementation (open-source or vendor) is mapped in for this build.
`include "rram_ctrl_bkdr_util_hier.svh"
`define RRAM_DATA_MEM_HIER    `RRAM_MACRO_HIER.`RRAM_DATA_MEM_PATH
`define RRAM_INFO_MEM_HIER    `RRAM_MACRO_HIER.`RRAM_INFO_MEM_PATH
// Describes the layout of the ROM memory array of whichever prim_rom implementation is mapped in
// for this build.
`include "rom_ctrl_bkdr_util_hier.svh"
`define ICACHE_WAY0_HIER      `CPU_CORE_HIER.gen_rams.gen_rams_inner[0].gen_scramble_rams
`define ICACHE_WAY1_HIER      `CPU_CORE_HIER.gen_rams.gen_rams_inner[1].gen_scramble_rams

// `..._MEM_INST_HIER` is the memory's `prim_ram_1p` instance. `..._MEM_PATH` is its HDL path
// string, used as the `path` arg of `mem_bkdr_util::new`/`sram_ctrl_bkdr_util::new`.
// `..._MEM_TILE_HIER` is the array itself, used by `$size()`/`$bits()`/`` `MEM_BKDR_UTIL_FILE_OP` ``;
// it's only defined for a never-tiled/bit-sliced memory.
`define ICACHE0_TAG_MEM_INST_HIER  `ICACHE_WAY0_HIER.tag_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem
`define ICACHE1_TAG_MEM_INST_HIER  `ICACHE_WAY1_HIER.tag_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem
`define ICACHE0_DATA_MEM_INST_HIER `ICACHE_WAY0_HIER.data_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem
`define ICACHE1_DATA_MEM_INST_HIER `ICACHE_WAY1_HIER.data_bank.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem
`define RAM_MAIN_MEM_INST_HIER     `RAM_MAIN_HIER.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem
`define RAM_RET_MEM_INST_HIER      `RAM_RET_HIER.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem
`define OTBN_IMEM_MEM_INST_HIER    `OTBN_HIER.u_imem.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem
`define OTBN_DMEM_MEM_INST_HIER    `OTBN_HIER.u_dmem.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem
`define USBDEV_BUF_MEM_INST_HIER   `USBDEV_HIER.gen_no_stubbed_memory.u_memory_1p.gen_ram_inst[0].u_mem
`include "mem_bkdr_util_hier.svh"

`define ICACHE0_TAG_MEM_PATH  `DV_STRINGIFY(`ICACHE0_TAG_MEM_INST_HIER.`ICACHE_TAG_MEM_TILE_PATH)
`define ICACHE1_TAG_MEM_PATH  `DV_STRINGIFY(`ICACHE1_TAG_MEM_INST_HIER.`ICACHE_TAG_MEM_TILE_PATH)
`define ICACHE0_DATA_MEM_PATH `DV_STRINGIFY(`ICACHE0_DATA_MEM_INST_HIER.`ICACHE_DATA_MEM_TILE_PATH)
`define ICACHE1_DATA_MEM_PATH `DV_STRINGIFY(`ICACHE1_DATA_MEM_INST_HIER.`ICACHE_DATA_MEM_TILE_PATH)
`define RAM_MAIN_MEM_TILE_HIER `RAM_MAIN_MEM_INST_HIER.`RAM_MAIN_MEM_TILE_PATH
`define RAM_MAIN_MEM_PATH      `RAM_MAIN_MEM_BKDR_PATH(`RAM_MAIN_MEM_INST_HIER)
`define RAM_RET_MEM_PATH       `DV_STRINGIFY(`RAM_RET_MEM_INST_HIER.`RAM_RET_MEM_TILE_PATH)
`define OTBN_IMEM_MEM_PATH     `DV_STRINGIFY(`OTBN_IMEM_MEM_INST_HIER.`OTBN_IMEM_MEM_TILE_PATH)
// OTBN_DMEM may be bit-sliced across several macro instances (see mem_bkdr_util_hier.svh), so its
// `path` needs the per-implementation `OTBN_DMEM_MEM_BKDR_PATH` macro-function, the same way
// RAM_MAIN's does for address-tiling.
`define OTBN_DMEM_MEM_PATH     `OTBN_DMEM_MEM_BKDR_PATH(`OTBN_DMEM_MEM_INST_HIER)
`define USBDEV_BUF_MEM_PATH    `DV_STRINGIFY(`USBDEV_BUF_MEM_INST_HIER.`USBDEV_BUF_MEM_TILE_PATH)

// `ROM_MEM_HIER` is the prim_rom instance and `ROM_MEM_TILE_HIER` the memory array of tile 0, from
// which the depth and the width of every tile are derived.  `ROM_MEM_PATH` is the `path` argument
// of `mem_bkdr_util::new`; the prim_rom implementation decides which of the two it is.
`define ROM_MEM_HIER          `ROM_CTRL_HIER.`ROM_CTRL_INT_PATH
`define ROM_MEM_TILE_HIER     `ROM_MEM_HIER.`ROM_MEM_TILE_PATH
`define ROM_MEM_PATH          `ROM_MEM_BKDR_PATH(`ROM_MEM_HIER)
