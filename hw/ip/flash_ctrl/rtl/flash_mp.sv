// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Memory Protection
//

`include "prim_assert.sv"

module flash_mp #(
  parameter int MpRegions = 8,
  parameter int NumBanks = 2,
  parameter int AllPagesW = 16,
  localparam int TotalRegions = MpRegions+1,
  localparam int BankW = $clog2(NumBanks)
) (
  input clk_i,
  input rst_ni,

  // configuration from sw
  input flash_ctrl_reg_pkg::flash_ctrl_reg2hw_mp_region_cfg_mreg_t [TotalRegions-1:0] region_cfgs_i,
  input flash_ctrl_reg_pkg::flash_ctrl_reg2hw_mp_bank_cfg_mreg_t [NumBanks-1:0] bank_cfgs_i,

  // interface signals to/from *_ctrl
  input req_i,
  input [AllPagesW-1:0] req_addr_i,
  input addr_ovfl_i,
  input [BankW-1:0] req_bk_i,
  input rd_i,
  input prog_i,
  input pg_erase_i,
  input bk_erase_i,
  output logic rd_done_o,
  output logic prog_done_o,
  output logic erase_done_o,
  output logic error_o,
  output logic [AllPagesW-1:0] err_addr_o,
  output logic [BankW-1:0] err_bank_o,

  // interface signals to/from flash_phy
  output logic req_o,
  output logic rd_o,
  output logic prog_o,
  output logic pg_erase_o,
  output logic bk_erase_o,
  input rd_done_i,
  input prog_done_i,
  input erase_done_i

);
  import flash_ctrl_pkg::*;

  // There could be multiple region matches due to region overlap
  logic [AllPagesW-1:0] region_end[TotalRegions];
  logic [TotalRegions-1:0] region_match;
  logic [TotalRegions-1:0] region_sel;
  logic [TotalRegions-1:0] rd_en;
  logic [TotalRegions-1:0] prog_en;
  logic [TotalRegions-1:0] pg_erase_en;
  logic [NumBanks-1:0] bk_erase_en;
  logic final_rd_en;
  logic final_prog_en;
  logic final_pg_erase_en;
  logic final_bk_erase_en;

  // Lower indices always have priority
  assign region_sel[0] = region_match[0];
  for (genvar i = 1; i < TotalRegions; i++) begin: gen_region_priority
    assign region_sel[i] = region_match[i] & ~|region_match[i-1:0];
  end

  // check for region match
  always_comb begin
    for (int unsigned i = 0; i < TotalRegions; i++) begin: region_comps
      region_end[i] = region_cfgs_i[i].base.q + region_cfgs_i[i].size.q;
      region_match[i] = req_addr_i >= region_cfgs_i[i].base.q &
                        req_addr_i <  region_end[i] &
                        req_i;

      rd_en[i] = region_cfgs_i[i].en.q & region_cfgs_i[i].rd_en.q & region_sel[i];
      prog_en[i] = region_cfgs_i[i].en.q & region_cfgs_i[i].prog_en.q & region_sel[i];
      pg_erase_en[i] = region_cfgs_i[i].en.q & region_cfgs_i[i].erase_en.q & region_sel[i];
    end
  end

  // check for bank erase
  always_comb begin
    for (int unsigned i = 0; i < NumBanks; i++) begin: bank_comps
      bk_erase_en[i] = (req_bk_i == i) & bank_cfgs_i[i].q;
    end
  end

  assign final_rd_en = rd_i & |rd_en;
  assign final_prog_en = prog_i & |prog_en;
  assign final_pg_erase_en = pg_erase_i & |pg_erase_en;
  assign final_bk_erase_en = bk_erase_i & |bk_erase_en;

  assign rd_o = req_i & final_rd_en;
  assign prog_o = req_i & final_prog_en;
  assign pg_erase_o = req_i & final_pg_erase_en;
  assign bk_erase_o = req_i & final_bk_erase_en;
  assign req_o = rd_o | prog_o | pg_erase_o | bk_erase_o;

  logic txn_err;
  logic txn_ens;
  logic no_allowed_txn;
  assign txn_ens = final_rd_en | final_prog_en | final_pg_erase_en | final_bk_erase_en;
  // if incoming address overflowed or no transaction enbales, error back
  assign no_allowed_txn = req_i & (addr_ovfl_i | ~txn_ens);

  // return done and error the next cycle
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      txn_err <= 1'b0;
      err_addr_o <= '0;
      err_bank_o <= '0;
    end else if (txn_err) begin
      txn_err <= 1'b0;
    end else if (no_allowed_txn) begin
      txn_err <= 1'b1;
      err_addr_o <= req_addr_i;
      err_bank_o <= req_bk_i;
    end
  end

  assign rd_done_o = rd_done_i | txn_err;
  assign prog_done_o = prog_done_i | txn_err;
  assign erase_done_o = erase_done_i | txn_err;
  assign error_o = txn_err;

  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  //////////////////////////////////////////////

  // Bank erase enable should always be one-hot.  We cannot erase multiple banks
  // at the same time
  `ASSERT(bkEraseEnOnehot_a, (req_o & bk_erase_o) |-> $onehot(bk_erase_en))
  // Requests can only happen one at a time
  `ASSERT(requestTypesOnehot_a, req_o |-> $onehot({rd_o, prog_o, pg_erase_o, bk_erase_o}))

endmodule // flash_erase_ctrl
