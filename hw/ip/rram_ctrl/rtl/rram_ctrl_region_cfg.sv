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

  // Emulated info page region (window) and subregion configuration.
  input sw_emul_info_regwen_t [EmulInfoRegions-1:0]              emul_info_regwen_i,
  input sw_emul_info_region_t [EmulInfoRegions-1:0]              emul_info_region_i,
  input sw_emul_info_subregion_regwen_t [EmulInfoSubregions-1:0] emul_info_subregion_regwen_i,
  input sw_emul_info_subregion_t [EmulInfoSubregions-1:0]        emul_info_subregion_i,
  input sw_emul_info_subregion_cfg_t [EmulInfoSubregions-1:0]    emul_info_subregion_cfg_i,

  // Combined page configurations for controller
  output mp_region_cfg_t region_cfgs_o[TotalMpRegions],
  // Combined page configurations for host (No access to emulated regions)
  output mp_region_cfg_t host_region_cfgs_o[HostMpRegions],
  output mp_info_cfg_t   info_page_cfgs_o[TotalInfoPages]
);

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_and_hi;
  import prim_mubi_pkg::mubi4_bool_to_mubi;

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
  // Priority layout (lowest index wins, see rram_ctrl_mp_region_sel):
  //   0                                                : OTP exclusion
  //   EmulInfoSubregionBase  .. EmulInfoWindowDenyBase-1  : emulated info subregions
  //   EmulInfoWindowDenyBase .. MpRegionBase-1            : emulated info window-deny entries
  //   MpRegionBase           .. DefaultRegionIdx-1        : configurable (generic) regions
  //   DefaultRegionIdx                                    : default region
  localparam int unsigned EmulInfoSubregionBase  = 1;
  localparam int unsigned EmulInfoWindowDenyBase = EmulInfoSubregionBase + EmulInfoSubregions;
  localparam int unsigned MpRegionBase           = EmulInfoWindowDenyBase + EmulInfoRegions;
  localparam int unsigned DefaultRegionIdx       = MpRegionBase + MpRegions;

  // Emulated info window-deny entries, one per window.
  // Denies any address not covered by an enabled subregion, so gaps never fall through.
  // Only deny once the window is locked.
  logic [EmulInfoRegions-1:0] window_locked;
  mp_region_cfg_t window_deny_cfg[EmulInfoRegions];
  for (genvar w = 0; w < EmulInfoRegions; w++) begin : gen_emul_info_window
    assign window_locked[w] = ~emul_info_regwen_i[w].q;

    assign window_deny_cfg[w].base  = emul_info_region_i[w].base.q;
    assign window_deny_cfg[w].size  = emul_info_region_i[w].size.q;
    assign window_deny_cfg[w].phase = PhaseInvalid;
    assign window_deny_cfg[w].cfg   = window_locked[w] ? CfgNoAccess : CfgDisable;
  end

  // Emulated info page subregions.
  // Each stores an offset relative to its window's base, TOR-style, passed straight into size.
  // Every subregion's base is simply its window's base.
  // Lower indices win, so a subregion's effective range is the prior one's end up to its own.
  // A subregion is enabled only once its own placement, the whole lock chain back to index 0,
  // and the window are all locked, and its offset fits within the window.
  logic [EmulInfoSubregions-1:0] chain_locked;
  mp_region_cfg_t subregion_cfg[EmulInfoSubregions];
  for (genvar i = 0; i < EmulInfoSubregions; i++) begin : gen_subregion
    localparam int unsigned WIdx = i / EmulInfoSubregionsPerRegion;

    logic placement_locked;
    logic overflow_ok;

    assign placement_locked = ~emul_info_subregion_regwen_i[i].q;

    if ((i % EmulInfoSubregionsPerRegion) == 0) begin : gen_chain_first
      assign chain_locked[i] = placement_locked & window_locked[WIdx];
    end else begin : gen_chain_rest
      assign chain_locked[i] = chain_locked[i-1] & placement_locked;
    end

    // Base is simply the window's base.
    // Priority alone carves out each subregion's range, as described above.
    assign subregion_cfg[i].base = emul_info_region_i[WIdx].base.q;
    assign subregion_cfg[i].size = PageW'(emul_info_subregion_i[i].q);

    // The subregion's and the window's size share the same base.
    // Overflow therefore reduces to a direct offset comparison.
    assign overflow_ok = PageW'(emul_info_subregion_i[i].q) <= emul_info_region_i[WIdx].size.q;

    assign subregion_cfg[i].phase           = PhaseInvalid;
    assign subregion_cfg[i].cfg.en          = mubi4_bool_to_mubi(chain_locked[i] & overflow_ok);
    assign subregion_cfg[i].cfg.rd_en       = mubi4_t'(emul_info_subregion_cfg_i[i].rd_en.q);
    assign subregion_cfg[i].cfg.wr_en       = mubi4_t'(emul_info_subregion_cfg_i[i].wr_en.q);
    assign subregion_cfg[i].cfg.scramble_en = mubi4_t'(emul_info_subregion_cfg_i[i].scramble_en.q);
    assign subregion_cfg[i].cfg.ecc_en      = mubi4_t'(emul_info_subregion_cfg_i[i].ecc_en.q);
    assign subregion_cfg[i].cfg.addr_xor_en = prim_mubi_pkg::MuBi4True;
  end

  // Configurable regions.
  mp_region_cfg_t generic_region_cfg[MpRegions];
  for (genvar i = 0; i < MpRegions; i++) begin : gen_mp_regions
    assign generic_region_cfg[i].base            = region_i[i].base.q;
    assign generic_region_cfg[i].size            = region_i[i].size.q;
    assign generic_region_cfg[i].cfg.en          = mubi4_t'(region_cfg_i[i].en.q);
    assign generic_region_cfg[i].cfg.rd_en       = mubi4_t'(region_cfg_i[i].rd_en.q);
    assign generic_region_cfg[i].cfg.wr_en       = mubi4_t'(region_cfg_i[i].wr_en.q);
    assign generic_region_cfg[i].cfg.scramble_en = mubi4_t'(region_cfg_i[i].scramble_en.q);
    assign generic_region_cfg[i].cfg.ecc_en      = mubi4_t'(region_cfg_i[i].ecc_en.q);
    assign generic_region_cfg[i].cfg.addr_xor_en = prim_mubi_pkg::MuBi4True;
    assign generic_region_cfg[i].phase           = PhaseInvalid;
  end

  // Default region is used if no other region matched.
  mp_region_cfg_t default_region_cfg;
  assign default_region_cfg.base            = '0;
  assign default_region_cfg.size            = TotalDataPages - 1;
  assign default_region_cfg.cfg.en          = prim_mubi_pkg::MuBi4True;
  assign default_region_cfg.cfg.rd_en       = mubi4_t'(default_cfg_i.rd_en.q);
  assign default_region_cfg.cfg.wr_en       = mubi4_t'(default_cfg_i.wr_en.q);
  assign default_region_cfg.cfg.scramble_en = mubi4_t'(default_cfg_i.scramble_en.q);
  assign default_region_cfg.cfg.ecc_en      = mubi4_t'(default_cfg_i.ecc_en.q);
  assign default_region_cfg.cfg.addr_xor_en = prim_mubi_pkg::MuBi4True;
  assign default_region_cfg.phase           = PhaseInvalid;

  // Combine into region_cfgs_o, in priority order (see the layout above).
  assign region_cfgs_o[0] = SwInitDataCfg;
  for (genvar i = 0; i < EmulInfoSubregions; i++) begin : gen_region_cfgs_subregion
    assign region_cfgs_o[EmulInfoSubregionBase + i] = subregion_cfg[i];
  end
  for (genvar w = 0; w < EmulInfoRegions; w++) begin : gen_region_cfgs_window_deny
    assign region_cfgs_o[EmulInfoWindowDenyBase + w] = window_deny_cfg[w];
  end
  for (genvar i = 0; i < MpRegions; i++) begin : gen_region_cfgs_mp_region
    assign region_cfgs_o[MpRegionBase + i] = generic_region_cfg[i];
  end
  assign region_cfgs_o[DefaultRegionIdx] = default_region_cfg;

  // Host requests always deny the OTP region and the whole emulated info regions, regardless of
  // subregion configuration.
  // Falls through to the same configurable and default regions as above.
  localparam int unsigned HostEmulInfoBase     = 1;
  localparam int unsigned HostMpRegionBase     = HostEmulInfoBase + EmulInfoRegions;
  localparam int unsigned HostDefaultRegionIdx = HostMpRegionBase + MpRegions;

  assign host_region_cfgs_o[0] = SwInitDataCfg;

  for (genvar w = 0; w < EmulInfoRegions; w++) begin : gen_host_emul_info_region
    assign host_region_cfgs_o[HostEmulInfoBase + w] = window_deny_cfg[w];
  end

  for (genvar i = 0; i < MpRegions; i++) begin : gen_host_mp_regions
    assign host_region_cfgs_o[HostMpRegionBase + i] = generic_region_cfg[i];
  end

  assign host_region_cfgs_o[HostDefaultRegionIdx] = default_region_cfg;

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
