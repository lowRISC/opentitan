// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM control region configuration processing
//
// This module:
// - translates all sw_region_rules into one array
// - translates all sw_info_cfg rules into one array
// - makes owner, creator, iso pages writeable depending on lc_configuration


module rram_ctrl_region_cfg
  import rram_ctrl_pkg::*;
(
  input logic clk_i,
  input logic rst_ni,

  // special page configuration from lc_ctrl
  input lc_ctrl_pkg::lc_tx_t lc_creator_seed_sw_rw_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_owner_seed_sw_rw_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_wr_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_rd_en_i,

  // All page configurations
  input sw_region_t [MpRegions-1:0]        region_i,
  input sw_region_cfg_t [MpRegions-1:0]    region_cfg_i,
  input sw_default_cfg_t                   default_cfg_i,
  input sw_info_cfg_t [TotalInfoPages-1:0] info_page_cfg_i,

  // Combined page configurations
  output mp_region_cfg_t region_cfgs_o[TotalMpRegions],
  output mp_info_cfg_t   info_page_cfgs_o[TotalInfoPages]
);

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_and_hi;

  //////////////////////////////////////
  // Life cycle synchronizer          //
  //////////////////////////////////////
  lc_ctrl_pkg::lc_tx_t lc_creator_seed_sw_rw_en;
  lc_ctrl_pkg::lc_tx_t lc_owner_seed_sw_rw_en;
  lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_rd_en;
  lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_wr_en;

  // Synchronize enables into local domain
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

  mubi4_t mubi_owner_sw_rw_en;
  mubi4_t mubi_creator_sw_rw_en;
  mubi4_t mubi_iso_sw_rd_en;
  mubi4_t mubi_iso_sw_wr_en;

  assign mubi_creator_sw_rw_en = lc_ctrl_pkg::lc_to_mubi4(lc_creator_seed_sw_rw_en);
  assign mubi_owner_sw_rw_en   = lc_ctrl_pkg::lc_to_mubi4(lc_owner_seed_sw_rw_en);
  assign mubi_iso_sw_rd_en     = lc_ctrl_pkg::lc_to_mubi4(lc_iso_part_sw_rd_en);
  assign mubi_iso_sw_wr_en     = lc_ctrl_pkg::lc_to_mubi4(lc_iso_part_sw_wr_en);

  //////////////////////////////////////
  // Data partition regions           //
  //////////////////////////////////////
  // Initial region: (prevent access to OTP section)
  // This region is located at index 0 such that it has the highest priority and cannot be
  // overruled by other regions
  assign region_cfgs_o[0] = SwInitDataCfg;

  // Configurable regions
  for (genvar i = 1; i <= MpRegions; i++) begin : gen_mp_regions
    assign region_cfgs_o[i].base            = region_i[i-1].base.q;
    assign region_cfgs_o[i].size            = region_i[i-1].size.q;
    assign region_cfgs_o[i].cfg.en          = mubi4_t'(region_cfg_i[i-1].en.q);
    assign region_cfgs_o[i].cfg.rd_en       = mubi4_t'(region_cfg_i[i-1].rd_en.q);
    assign region_cfgs_o[i].cfg.wr_en       = mubi4_t'(region_cfg_i[i-1].wr_en.q);
    assign region_cfgs_o[i].cfg.scramble_en = mubi4_t'(region_cfg_i[i-1].scramble_en.q);
    assign region_cfgs_o[i].cfg.ecc_en      = mubi4_t'(region_cfg_i[i-1].ecc_en.q);
    assign region_cfgs_o[i].cfg.addr_xor_en = prim_mubi_pkg::MuBi4True;
    assign region_cfgs_o[i].phase           = PhaseInvalid;
  end

  // Default region applies if no other region matched
  assign region_cfgs_o[MpRegions+1].base            = '0;
  assign region_cfgs_o[MpRegions+1].size            = TotalPages - 1;
  assign region_cfgs_o[MpRegions+1].cfg.en          = prim_mubi_pkg::MuBi4True;
  assign region_cfgs_o[MpRegions+1].cfg.rd_en       = mubi4_t'(default_cfg_i.rd_en.q);
  assign region_cfgs_o[MpRegions+1].cfg.wr_en       = mubi4_t'(default_cfg_i.wr_en.q);
  assign region_cfgs_o[MpRegions+1].cfg.scramble_en = mubi4_t'(default_cfg_i.scramble_en.q);
  assign region_cfgs_o[MpRegions+1].cfg.ecc_en      = mubi4_t'(default_cfg_i.ecc_en.q);
  assign region_cfgs_o[MpRegions+1].cfg.addr_xor_en = prim_mubi_pkg::MuBi4True;
  assign region_cfgs_o[MpRegions+1].phase           = PhaseInvalid;

  /////////////////////////////////////////////
  // Info partition properties configuration //
  /////////////////////////////////////////////
  for (genvar i = 0; i < TotalInfoPages; i++) begin : gen_info_page
    mubi4_t reg_en;
    mubi4_t reg_wr_en;
    mubi4_t reg_rd_en;
    mubi4_t reg_scramble_en;
    mubi4_t reg_ecc_en;

    assign reg_en          = mubi4_t'(info_page_cfg_i[i].en.q);
    assign reg_rd_en       = mubi4_t'(info_page_cfg_i[i].rd_en.q);
    assign reg_wr_en       = mubi4_t'(info_page_cfg_i[i].wr_en.q);
    assign reg_scramble_en = mubi4_t'(info_page_cfg_i[i].scramble_en.q);
    assign reg_ecc_en      = mubi4_t'(info_page_cfg_i[i].ecc_en.q);

    assign info_page_cfgs_o[i].page            = InfoPageW'(unsigned'(i));
    assign info_page_cfgs_o[i].phase           = PhaseInvalid;
    assign info_page_cfgs_o[i].cfg.scramble_en = reg_scramble_en;
    assign info_page_cfgs_o[i].cfg.ecc_en      = reg_ecc_en;
    assign info_page_cfgs_o[i].cfg.addr_xor_en = prim_mubi_pkg::MuBi4True;
    assign info_page_cfgs_o[i].cfg.en          = reg_en;

    // Creator, owner, and isolated info page configuration can be overruled by the life-cycle
    // controller
    if (i == CreatorInfoPage) begin : gen_creator_info_page
      assign info_page_cfgs_o[i].cfg.rd_en = mubi4_and_hi(reg_rd_en, mubi_creator_sw_rw_en);
      assign info_page_cfgs_o[i].cfg.wr_en = mubi4_and_hi(reg_wr_en, mubi_creator_sw_rw_en);
    end else if (i == OwnerInfoPage) begin : gen_owner_info_page
      assign info_page_cfgs_o[i].cfg.rd_en = mubi4_and_hi(reg_rd_en, mubi_owner_sw_rw_en);
      assign info_page_cfgs_o[i].cfg.wr_en = mubi4_and_hi(reg_wr_en, mubi_owner_sw_rw_en);
    end else if (i == IsolatedInfoPage) begin : gen_isolated_info_page
      assign info_page_cfgs_o[i].cfg.rd_en = mubi4_and_hi(reg_rd_en, mubi_iso_sw_rd_en);
      assign info_page_cfgs_o[i].cfg.wr_en = mubi4_and_hi(reg_wr_en, mubi_iso_sw_wr_en);
    end else begin : gen_generic_info_page
      assign info_page_cfgs_o[i].cfg.rd_en = reg_rd_en;
      assign info_page_cfgs_o[i].cfg.wr_en = reg_wr_en;
    end
  end

endmodule // rram_ctrl_region_cfg
