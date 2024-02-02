// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash info page protection assignment
// This module takes into account seed pages and assigns privileges accordingly.

`include "prim_assert.sv"

module flash_ctrl_info_cfg import flash_ctrl_pkg::*; # (
  parameter logic [BankW-1:0] Bank = 0,
  parameter logic [InfoTypesWidth-1:0] InfoSel = 0
) (
  input  clk_i,
  input  rst_ni,
  input  info_page_cfg_t [InfosPerBank-1:0] cfgs_i,
  input  creator_seed_priv_i,
  input  owner_seed_priv_i,
  input  iso_flash_wr_en_i,
  input  iso_flash_rd_en_i,
  output info_page_cfg_t [InfosPerBank-1:0] cfgs_o
);

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::mubi4_bool_to_mubi;

  info_page_cfg_t creator_seed_qual, owner_seed_qual, isolate_qual;

  mubi4_t creator_en;
  prim_mubi4_sender #(
    .AsyncOn(0),
    .EnSecBuf(1)
  ) u_creator_mubi (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi4_bool_to_mubi(creator_seed_priv_i)),
    .mubi_o(creator_en)
  );

  mubi4_t owner_en;
  prim_mubi4_sender #(
    .AsyncOn(0),
    .EnSecBuf(1)
  ) u_owner_mubi (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi4_bool_to_mubi(owner_seed_priv_i)),
    .mubi_o(owner_en)
  );

  assign creator_seed_qual = '{
    en: creator_en,
    rd_en: creator_en,
    prog_en: creator_en,
    erase_en: creator_en,
    scramble_en: MuBi4True,
    ecc_en: MuBi4True,
    he_en : MuBi4True
  };

  assign owner_seed_qual = '{
    en: owner_en,
    rd_en: owner_en,
    prog_en: owner_en,
    erase_en: owner_en,
    scramble_en: MuBi4True,
    ecc_en: MuBi4True,
    he_en : MuBi4True
  };

  assign isolate_qual = '{
    en: MuBi4True,
    rd_en: mubi4_bool_to_mubi(iso_flash_rd_en_i),
    prog_en: mubi4_bool_to_mubi(iso_flash_wr_en_i),
    erase_en: mubi4_bool_to_mubi(iso_flash_wr_en_i),
    scramble_en: MuBi4True,
    ecc_en: MuBi4True,
    he_en : MuBi4True
  };

  // The code below uses page_addr_t to represent a page inside an Info partition, but a page_addr_t
  // is really designed a page inside a Data partition (the "addr" field has width BankW + PageW,
  // not BankW + InfoPageW). This will work just fine so long as InfoPageW <= PageW, but we should
  // check that's always true.
  `ASSERT_INIT(InfoNoBiggerThanData_A, InfoPageW <= PageW)

  for (genvar i = 0; i < InfosPerBank; i++) begin : gen_info_priv

    localparam logic [InfoPageW-1:0] CurPage = i;
    localparam page_addr_t CurAddr = '{sel: InfoSel, addr: {Bank, PageW'(CurPage)}};

    if (i > InfoTypeSize[InfoSel]) begin : gen_invalid_region
      assign cfgs_o[i] = CfgInfoDisable;

      // For info types that have fewer pages than the maximum, not the full config (cfgs_i[i] for i
      // greater than InfoTypeSize[InfoSel]) is used.
      info_page_cfg_t unused_cfgs;
      assign unused_cfgs = cfgs_i[i];

    // if match creator, only allow access when creator privilege is set
    end else if (CurAddr == SeedInfoPageSel[CreatorSeedIdx]) begin : gen_creator
      assign cfgs_o[i] = info_cfg_qual(cfgs_i[i], creator_seed_qual);

    // if match owner, only allow access when owner privilege is set
    end else if (CurAddr == SeedInfoPageSel[OwnerSeedIdx]) begin : gen_owner
      assign cfgs_o[i] = info_cfg_qual(cfgs_i[i], owner_seed_qual);

    // if match isolated partition, only allow read when provision privilege is set
    end else if (CurAddr == IsolatedPageSel) begin : gen_isolated_page
      assign cfgs_o[i] = info_cfg_qual(cfgs_i[i], isolate_qual);

      // since certain fields will always be 0'd out based on mubi values,
      // the software input will look like it is unused to lint
      info_page_cfg_t unused_cfgs;
      assign unused_cfgs = cfgs_i[i];

    // if other, just passthrough configuration
    end else begin : gen_normal
      assign cfgs_o[i] = cfgs_i[i];
    end
  end

  // if bank does not contain seed pages, tie off the privilege signals
  if (SeedBank != Bank || SeedInfoSel != InfoSel) begin : gen_tieoffs
    info_page_cfg_t unused_pg_cfg;
    assign unused_pg_cfg = creator_seed_qual^owner_seed_qual^isolate_qual;
  end




endmodule // flash_ctrl_info_cfg
