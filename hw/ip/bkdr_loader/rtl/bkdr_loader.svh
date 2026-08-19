// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef BKDR_LOADER_SVH
`define BKDR_LOADER_SVH

`define BKDR_LOADER_CONNECT_REQS \
  assign top_earlgrey.earlgrey_pd_aon.u_sram_ctrl_ret.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_req   = bkdr_req[bkdr_loader_pkg::BkdrAon];      \
  assign top_earlgrey.earlgrey_pd_main.u_rram_macro.u_info_array.bkdr_req                                                  = bkdr_req[bkdr_loader_pkg::BkdrRramInfo]; \
  assign top_earlgrey.earlgrey_pd_main.u_rram_macro.u_data_array.bkdr_req                                                  = bkdr_req[bkdr_loader_pkg::BkdrRramData]; \
  assign top_earlgrey.earlgrey_pd_main.u_sram_ctrl_main.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_req = bkdr_req[bkdr_loader_pkg::BkdrSram];     \
  assign top_earlgrey.earlgrey_pd_main.u_sram_ctrl_sec.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_req  = bkdr_req[bkdr_loader_pkg::BkdrSramSec];  \
  assign top_earlgrey.earlgrey_pd_main.u_sram_ctrl_meta.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_req = bkdr_req[bkdr_loader_pkg::BkdrSramMeta]; \
  assign top_earlgrey.earlgrey_pd_main.u_rom_ctrl.gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom.bkdr_req                 = bkdr_req[bkdr_loader_pkg::BkdrRom];

`define BKDR_LOADER_CONNECT_RSPS \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrAon]      = top_earlgrey.earlgrey_pd_aon.u_sram_ctrl_ret.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_rsp;   \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrRramInfo] = top_earlgrey.earlgrey_pd_main.u_rram_macro.u_info_array.bkdr_rsp;                                                  \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrRramData] = top_earlgrey.earlgrey_pd_main.u_rram_macro.u_data_array.bkdr_rsp;                                                  \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrSram]     = top_earlgrey.earlgrey_pd_main.u_sram_ctrl_main.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_rsp; \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrSramSec]  = top_earlgrey.earlgrey_pd_main.u_sram_ctrl_sec.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_rsp;  \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrSramMeta] = top_earlgrey.earlgrey_pd_main.u_sram_ctrl_meta.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].u_mem.bkdr_rsp; \
  assign bkdr_rsp[bkdr_loader_pkg::BkdrRom]      = top_earlgrey.earlgrey_pd_main.u_rom_ctrl.gen_rom_scramble_enabled.u_rom.u_rom.u_prim_rom.bkdr_rsp;

`endif
