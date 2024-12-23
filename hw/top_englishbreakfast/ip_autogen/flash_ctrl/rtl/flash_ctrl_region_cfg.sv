// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash control region configuration processing
//
// There are two main purpose of this module:
// 1. strip the error conditions away from reg packages (see #8282)
// 2. generate shadow update and storage errors

module flash_ctrl_region_cfg
  import flash_ctrl_pkg::*;
  import flash_ctrl_reg_pkg::*;
(
  input clk_i,
  input rst_ni,
  input lc_ctrl_pkg::lc_tx_t lc_creator_seed_sw_rw_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_owner_seed_sw_rw_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_wr_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_rd_en_i,
  input sw_bank_cfg_t [NumBanks-1:0] bank_cfg_i,
  input sw_region_t [MpRegions-1:0] region_i,
  input sw_region_cfg_t [MpRegions-1:0] region_cfg_i,
  input sw_default_cfg_t default_cfg_i,
  input sw_info_cfg_t [NumInfos0-1:0] bank0_info0_cfg_i,
  input sw_info_cfg_t [NumInfos1-1:0] bank0_info1_cfg_i,
  input sw_info_cfg_t [NumInfos2-1:0] bank0_info2_cfg_i,
  input sw_info_cfg_t [NumInfos0-1:0] bank1_info0_cfg_i,
  input sw_info_cfg_t [NumInfos1-1:0] bank1_info1_cfg_i,
  input sw_info_cfg_t [NumInfos2-1:0] bank1_info2_cfg_i,

  output bank_cfg_t [NumBanks-1:0] bank_cfg_o,
  output mp_region_cfg_t [MpRegions:0] region_cfgs_o,
  output info_page_cfg_t [NumBanks-1:0][InfoTypes-1:0][InfosPerBank-1:0] info_page_cfgs_o
);

  import prim_mubi_pkg::mubi4_t;

  //////////////////////////////////////
  // Life cycle synchronizer
  //////////////////////////////////////

  lc_ctrl_pkg::lc_tx_t lc_creator_seed_sw_rw_en;
  lc_ctrl_pkg::lc_tx_t lc_owner_seed_sw_rw_en;
  lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_rd_en;
  lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_wr_en;

  // synchronize enables into local domain
  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_creator_seed_sw_rw_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_creator_seed_sw_rw_en_i),
    .lc_en_o({lc_creator_seed_sw_rw_en})
  );

  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_owner_seed_sw_rw_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_owner_seed_sw_rw_en_i),
    .lc_en_o({lc_owner_seed_sw_rw_en})
  );

  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_iso_part_sw_rd_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_iso_part_sw_rd_en_i),
    .lc_en_o({lc_iso_part_sw_rd_en})
  );

  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_iso_part_sw_wr_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_iso_part_sw_wr_en_i),
    .lc_en_o({lc_iso_part_sw_wr_en})
  );

  //////////////////////////////////////
  // Bank speicfic configuration
  //////////////////////////////////////
  for (genvar i = 0; i < NumBanks; i++) begin : gen_bank_cfg
    assign bank_cfg_o[i].q = bank_cfg_i[i].q;
  end

  //////////////////////////////////////
  // Data partition regions
  //////////////////////////////////////
  // extra region is the default region
  for (genvar i = 0; i < MpRegions; i++) begin : gen_mp_regions
    assign region_cfgs_o[i].base        = region_i[i].base.q;
    assign region_cfgs_o[i].size        = region_i[i].size.q;
    assign region_cfgs_o[i].en          = mubi4_t'(region_cfg_i[i].en.q);
    assign region_cfgs_o[i].rd_en       = mubi4_t'(region_cfg_i[i].rd_en.q);
    assign region_cfgs_o[i].prog_en     = mubi4_t'(region_cfg_i[i].prog_en.q);
    assign region_cfgs_o[i].erase_en    = mubi4_t'(region_cfg_i[i].erase_en.q);
    assign region_cfgs_o[i].scramble_en = mubi4_t'(region_cfg_i[i].scramble_en.q);
    assign region_cfgs_o[i].ecc_en      = mubi4_t'(region_cfg_i[i].ecc_en.q);
    assign region_cfgs_o[i].he_en       = mubi4_t'(region_cfg_i[i].he_en.q);
  end

  //default region
  assign region_cfgs_o[MpRegions].base        = '0;
  assign region_cfgs_o[MpRegions].size        = NumBanks * PagesPerBank;
  assign region_cfgs_o[MpRegions].en          = prim_mubi_pkg::MuBi4True;
  assign region_cfgs_o[MpRegions].rd_en       = mubi4_t'(default_cfg_i.rd_en.q);
  assign region_cfgs_o[MpRegions].prog_en     = mubi4_t'(default_cfg_i.prog_en.q);
  assign region_cfgs_o[MpRegions].erase_en    = mubi4_t'(default_cfg_i.erase_en.q);
  assign region_cfgs_o[MpRegions].scramble_en = mubi4_t'(default_cfg_i.scramble_en.q);
  assign region_cfgs_o[MpRegions].ecc_en      = mubi4_t'(default_cfg_i.ecc_en.q);
  assign region_cfgs_o[MpRegions].he_en       = mubi4_t'(default_cfg_i.he_en.q);

  //////////////////////////////////////
  // Info partition properties configuration
  //////////////////////////////////////
  sw_info_cfg_t   [NumBanks-1:0][InfoTypes-1:0][InfosPerBank-1:0] sw_info_cfgs;
  info_page_cfg_t [NumBanks-1:0][InfoTypes-1:0][InfosPerBank-1:0] info_cfgs;
  localparam int InfoBits = $bits(sw_info_cfg_t) * InfosPerBank;

  // transform from unique names reg output to structure
  // Not all types have the maximum number of banks, so those are packed to 0
  assign sw_info_cfgs[0][0] = InfoBits'(bank0_info0_cfg_i);
  assign sw_info_cfgs[0][1] = InfoBits'(bank0_info1_cfg_i);
  assign sw_info_cfgs[0][2] = InfoBits'(bank0_info2_cfg_i);
  assign sw_info_cfgs[1][0] = InfoBits'(bank1_info0_cfg_i);
  assign sw_info_cfgs[1][1] = InfoBits'(bank1_info1_cfg_i);
  assign sw_info_cfgs[1][2] = InfoBits'(bank1_info2_cfg_i);

  // strip error indications
  for (genvar i = 0; i < NumBanks; i++) begin : gen_info_cfg_bank
    for (genvar j = 0; j < InfoTypes; j++) begin : gen_info_cfg_type
      for (genvar k = 0; k < InfosPerBank; k++) begin : gen_info_cfg_page
        assign info_cfgs[i][j][k].en          = mubi4_t'(sw_info_cfgs[i][j][k].en.q);
        assign info_cfgs[i][j][k].rd_en       = mubi4_t'(sw_info_cfgs[i][j][k].rd_en.q);
        assign info_cfgs[i][j][k].prog_en     = mubi4_t'(sw_info_cfgs[i][j][k].prog_en.q);
        assign info_cfgs[i][j][k].erase_en    = mubi4_t'(sw_info_cfgs[i][j][k].erase_en.q);
        assign info_cfgs[i][j][k].scramble_en = mubi4_t'(sw_info_cfgs[i][j][k].scramble_en.q);
        assign info_cfgs[i][j][k].ecc_en      = mubi4_t'(sw_info_cfgs[i][j][k].ecc_en.q);
        assign info_cfgs[i][j][k].he_en       = mubi4_t'(sw_info_cfgs[i][j][k].he_en.q);
      end
    end
  end

  import lc_ctrl_pkg::lc_tx_test_true_strict;

  // qualify software settings with creator / owner privileges
  for(genvar i = 0; i < NumBanks; i++) begin : gen_info_priv_bank
    for (genvar j = 0; j < InfoTypes; j++) begin : gen_info_priv_type
      flash_ctrl_info_cfg # (
        .Bank(i),
        .InfoSel(j)
      ) u_info_cfg (
        .clk_i,
        .rst_ni,
        .cfgs_i(info_cfgs[i][j]),
        .creator_seed_priv_i(lc_tx_test_true_strict(lc_creator_seed_sw_rw_en)),
        .owner_seed_priv_i(lc_tx_test_true_strict(lc_owner_seed_sw_rw_en)),
        .iso_flash_wr_en_i(lc_tx_test_true_strict(lc_iso_part_sw_wr_en)),
        .iso_flash_rd_en_i(lc_tx_test_true_strict(lc_iso_part_sw_rd_en)),
        .cfgs_o(info_page_cfgs_o[i][j])
      );
    end
  end

endmodule // flash_ctrl_reg_wrap
