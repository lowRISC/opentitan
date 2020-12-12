// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash info page protection assignment
// This module takes into account seed pages and assigns privileges accordingly.

`include "prim_assert.sv"

module flash_ctrl_info_cfg import flash_ctrl_pkg::*; # (
  parameter logic [BankW-1:0] Bank = 0,
  parameter int InfoSel = 0
) (
  input info_page_cfg_t [InfosPerBank-1:0] cfgs_i,
  input creator_seed_priv_i,
  input owner_seed_priv_i,
  input iso_flash_wr_en_i,
  input iso_flash_rd_en_i,
  output info_page_cfg_t [InfosPerBank-1:0] cfgs_o
);

  localparam int CfgBitWidth = $bits(info_page_cfg_t);
  info_page_cfg_t isolate_pg_cfg;
  assign isolate_pg_cfg = '{
    en: 1'b1,
    rd_en: iso_flash_rd_en_i,
    prog_en: iso_flash_wr_en_i,
    erase_en: iso_flash_wr_en_i,
    scramble_en: 1'b1,
    ecc_en: 1'b1,
    he_en : 1'b1
  };

  for(genvar i = 0; i < InfosPerBank; i++) begin : gen_info_priv

    localparam logic [InfoPageW-1:0] CurPage = i;
    localparam page_addr_t CurAddr = '{sel: InfoSel, addr: {Bank, CurPage}};

    if (i > InfoTypeSize[InfoSel]) begin : gen_invalid_region
      assign cfgs_o[i] = '0;

    // if match creator, only allow access when creator privilege is set
    end else if (CurAddr == SeedInfoPageSel[CreatorSeedIdx]) begin : gen_creator
      assign cfgs_o[i] = cfgs_i[i] & {CfgBitWidth{creator_seed_priv_i}};

    // if match owner, only allow access when owner privilege is set
    end else if (CurAddr == SeedInfoPageSel[OwnerSeedIdx]) begin : gen_owner
      assign cfgs_o[i] = cfgs_i[i] & {CfgBitWidth{owner_seed_priv_i}};

    // if match isolated partition, only allow read when provision privilege is set
    end else if (CurAddr == IsolatedPageSel) begin : gen_isolated_page
      assign cfgs_o[i] = cfgs_i[i] & isolate_pg_cfg;

    // if other, just passthrough configuration
    end else begin : gen_normal
      assign cfgs_o[i] = cfgs_i[i];
    end
  end

  // if bank does not contain seed pages, tie off the privilege signals
  if (SeedBank != Bank || SeedInfoSel != InfoSel) begin : gen_tieoffs
    logic [1:0] unused_seed_privs;
    assign unused_seed_privs = {owner_seed_priv_i, creator_seed_priv_i};
    info_page_cfg_t unused_pg_cfg;
    assign unused_pg_cfg = isolate_pg_cfg;
  end




endmodule // flash_ctrl_info_cfg
