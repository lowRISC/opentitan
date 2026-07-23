// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef BKDR_LOADER_SVH
`define BKDR_LOADER_SVH

`define BKDR_LOADER_CONNECT_REQS \
  assign top_earlgrey.earlgrey_pd_aon.u_sram_ctrl_ret.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_req                             = bkdr_req[bkdr_loader_pkg::BkdrAon];       \
  assign top_earlgrey.earlgrey_pd_main.u_rram_macro.u_info_array.bkdr_req                                                                            = bkdr_req[bkdr_loader_pkg::BkdrRramInfo];  \
  assign top_earlgrey.earlgrey_pd_main.u_rram_macro.u_data_array.bkdr_req                                                                            = bkdr_req[bkdr_loader_pkg::BkdrRramData];  \
  assign top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[1].u_prim_flash_bank.gen_info_types[2].u_info_mem.bkdr_req = bkdr_req[bkdr_loader_pkg::BkdrFlashB1I2]; \
  assign top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[1].u_prim_flash_bank.gen_info_types[1].u_info_mem.bkdr_req = bkdr_req[bkdr_loader_pkg::BkdrFlashB1I1]; \
  assign top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[1].u_prim_flash_bank.gen_info_types[0].u_info_mem.bkdr_req = bkdr_req[bkdr_loader_pkg::BkdrFlashB1I0]; \
  assign top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[1].u_prim_flash_bank.u_mem.bkdr_req                        = bkdr_req[bkdr_loader_pkg::BkdrFlashB1];   \
  assign top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[0].u_prim_flash_bank.gen_info_types[2].u_info_mem.bkdr_req = bkdr_req[bkdr_loader_pkg::BkdrFlashB0I2]; \
  assign top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[0].u_prim_flash_bank.gen_info_types[1].u_info_mem.bkdr_req = bkdr_req[bkdr_loader_pkg::BkdrFlashB0I1]; \
  assign top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[0].u_prim_flash_bank.gen_info_types[0].u_info_mem.bkdr_req = bkdr_req[bkdr_loader_pkg::BkdrFlashB0I0]; \
  assign top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[0].u_prim_flash_bank.u_mem.bkdr_req                        = bkdr_req[bkdr_loader_pkg::BkdrFlashB0];   \
  assign top_earlgrey.earlgrey_pd_main.u_sram_ctrl_main.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_req                           = bkdr_req[bkdr_loader_pkg::BkdrSram];      \
  assign top_earlgrey.earlgrey_pd_main.u_rom_ctrl.gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom.bkdr_req                                           = bkdr_req[bkdr_loader_pkg::BkdrRom];       \
  assign top_earlgrey.earlgrey_pd_main.u_otp_macro.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_req                                                  = bkdr_req[bkdr_loader_pkg::BkdrOtp];

`define BKDR_LOADER_CONNECT_RSPS \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrAon]       = top_earlgrey.earlgrey_pd_aon.u_sram_ctrl_ret.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_rsp;                             \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrRramInfo]  = top_earlgrey.earlgrey_pd_main.u_rram_macro.u_info_array.bkdr_rsp;                                                                            \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrRramData]  = top_earlgrey.earlgrey_pd_main.u_rram_macro.u_data_array.bkdr_rsp;                                                                            \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrFlashB1I2] = top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[1].u_prim_flash_bank.gen_info_types[2].u_info_mem.bkdr_rsp; \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrFlashB1I1] = top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[1].u_prim_flash_bank.gen_info_types[1].u_info_mem.bkdr_rsp; \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrFlashB1I0] = top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[1].u_prim_flash_bank.gen_info_types[0].u_info_mem.bkdr_rsp; \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrFlashB1]   = top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[1].u_prim_flash_bank.u_mem.bkdr_rsp;                        \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrFlashB0I2] = top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[0].u_prim_flash_bank.gen_info_types[2].u_info_mem.bkdr_rsp; \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrFlashB0I1] = top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[0].u_prim_flash_bank.gen_info_types[1].u_info_mem.bkdr_rsp; \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrFlashB0I0] = top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[0].u_prim_flash_bank.gen_info_types[0].u_info_mem.bkdr_rsp; \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrFlashB0]   = top_earlgrey.earlgrey_pd_main.u_flash_ctrl.u_eflash.u_flash.gen_prim_flash_banks[0].u_prim_flash_bank.u_mem.bkdr_rsp;                        \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrSram]      = top_earlgrey.earlgrey_pd_main.u_sram_ctrl_main.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_rsp;                           \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrRom]       = top_earlgrey.earlgrey_pd_main.u_rom_ctrl.gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom.bkdr_rsp;                                           \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrOtp]       = top_earlgrey.earlgrey_pd_main.u_otp_macro.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_rsp;

`endif
