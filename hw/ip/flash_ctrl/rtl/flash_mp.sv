// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Memory Protection
//

`include "prim_assert.sv"

module flash_mp import flash_ctrl_pkg::*; import flash_ctrl_reg_pkg::*; (
  input clk_i,
  input rst_ni,

  // interface selection
  input flash_sel_e if_sel_i,

  // configuration from sw
  input flash_ctrl_reg2hw_mp_region_cfg_mreg_t [MpRegions:0] region_cfgs_i,
  input flash_ctrl_reg2hw_mp_bank_cfg_mreg_t [NumBanks-1:0] bank_cfgs_i,
  input info_page_cfg_t [NumBanks-1:0][InfosPerBank-1:0] info_page_cfgs_i,

  // interface signals to/from *_ctrl
  input req_i,
  input [AllPagesW-1:0] req_addr_i,
  input flash_part_e req_part_i,
  input addr_ovfl_i,
  input rd_i,
  input prog_i,
  input pg_erase_i,
  input bk_erase_i,
  output logic rd_done_o,
  output logic prog_done_o,
  output logic erase_done_o,
  output logic error_o,
  output logic [AllPagesW-1:0] err_addr_o,

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

  // Total number of regions including default region
  localparam int TotalRegions = MpRegions+1;

  // bank + page address
  logic [AllPagesW-1:0] bank_page_addr;
  // bank address
  logic [BankW-1:0] bank_addr;
  // page address
  logic [PageW-1:0] page_addr;

  assign bank_page_addr = req_addr_i;
  assign bank_addr = req_addr_i[AllPagesW-1 -: BankW];
  assign page_addr = req_addr_i[PageW-1:0];

  // There could be multiple region matches due to region overlap
  // region_end is +1 bit from however many bits are needed to address regions
  logic [AllPagesW:0] region_end[TotalRegions];
  logic [TotalRegions-1:0] region_match;
  logic [TotalRegions-1:0] region_sel;
  logic [TotalRegions-1:0] rd_en;
  logic [TotalRegions-1:0] prog_en;
  logic [TotalRegions-1:0] pg_erase_en;
  logic [NumBanks-1:0] bk_erase_en;
  logic data_rd_en;
  logic data_prog_en;
  logic data_pg_erase_en;
  logic data_bk_erase_en;
  logic info_rd_en;
  logic info_prog_en;
  logic info_erase_en;

  // TBD handle memory protection for hardware initiated transactions
  logic hw_sel;

  ////////////////////////////////////////
  // Check address out of bounds
  // Applies for all partitions
  ////////////////////////////////////////
  logic addr_invalid;
  logic bank_invalid;
  logic [PageW-1:0] end_addr;

  // when number of banks are power of 2, invalid bank is handled by addr_ovfl_i
  if (NumBanks % 2 > 0) begin : gen_bank_check
    assign bank_invalid = bank_addr > NumBanks;
  end else begin : gen_no_bank_check
    logic [BankW-1:0] unused_bank_addr;
    assign unused_bank_addr = bank_addr;
    assign bank_invalid = '0;
  end

  // address is invalid if:
  // the address extends beyond the end of the partition in question
  // the bank selection is invalid
  // if the address overflowed the control counters
  assign end_addr = PartitionEndAddr[req_part_i];
  assign addr_invalid = req_i &
                        (page_addr > end_addr |
                         bank_invalid |
                         addr_ovfl_i
                        );

  ////////////////////////////////////////
  // Check data partition access
  ////////////////////////////////////////
  // Lower indices always have priority
  logic invalid_data_txn;

  assign region_sel[0] = region_match[0];
  for (genvar i = 1; i < TotalRegions; i++) begin: gen_region_priority
    assign region_sel[i] = region_match[i] & ~|region_match[i-1:0];
  end

  // check for region match
  always_comb begin
    for (int unsigned i = 0; i < TotalRegions; i++) begin: region_comps
      region_end[i] = {1'b0, region_cfgs_i[i].base.q} + region_cfgs_i[i].size.q;

      // region matches if address within range and if the partition matches
      region_match[i] = (bank_page_addr >= region_cfgs_i[i].base.q) &
                        ({1'b0, bank_page_addr} < region_end[i]) &
                        region_cfgs_i[i].en.q &
                        req_i;

      rd_en[i] =  region_cfgs_i[i].rd_en.q & region_sel[i];
      prog_en[i] = region_cfgs_i[i].prog_en.q & region_sel[i];
      pg_erase_en[i] = region_cfgs_i[i].erase_en.q & region_sel[i];
    end
  end

  // check for bank erase
  // bank erase allowed for only data partition
  always_comb begin
    for (int unsigned i = 0; i < NumBanks; i++) begin: bank_comps
      bk_erase_en[i] = (bank_addr == i) & bank_cfgs_i[i].q;
    end
  end

  assign data_rd_en = rd_i & |rd_en;
  assign data_prog_en = prog_i & |prog_en;
  assign data_pg_erase_en = pg_erase_i & |pg_erase_en;
  assign data_bk_erase_en = bk_erase_i & |bk_erase_en;

  // temporarily suppress errors on the hardware interface
  assign invalid_data_txn = req_i & req_part_i == FlashPartData & ~hw_sel &
                            ~(data_rd_en |
                              data_prog_en |
                              data_pg_erase_en |
                              data_bk_erase_en
                             );

  ////////////////////////////////////////
  // Check info partition access
  ////////////////////////////////////////
  logic [InfoPageW-1:0] info_page_addr;
  info_page_cfg_t page_cfg;
  logic info_en;
  logic invalid_info_txn;

  assign info_page_addr = req_addr_i[InfoPageW-1:0];
  assign page_cfg = info_page_cfgs_i[bank_addr][info_page_addr];

  assign info_en = page_cfg.en.q;
  assign info_rd_en = info_en & rd_i & page_cfg.rd_en.q;
  assign info_prog_en = info_en & prog_i & page_cfg.prog_en.q;
  assign info_erase_en = info_en & pg_erase_i & page_cfg.erase_en.q;

  assign invalid_info_txn = req_i & req_part_i == FlashPartInfo & ~hw_sel &
                            ~(info_rd_en | info_prog_en | info_erase_en);


  ////////////////////////////////////////
  // Combine all check results
  ////////////////////////////////////////
  // TBD properly account for hardware interface later
  // right now, hardwire transaction to go through
  logic hw_rd_en;
  logic hw_erase_en;
  assign hw_sel = if_sel_i == HwSel;
  assign hw_rd_en = rd_i & hw_sel;
  assign hw_erase_en = pg_erase_i & hw_sel;

  assign rd_o = req_i & (data_rd_en | info_rd_en | hw_rd_en);
  assign prog_o = req_i & data_prog_en;
  assign pg_erase_o = req_i & (data_pg_erase_en | info_erase_en | hw_erase_en);
  assign bk_erase_o = req_i & data_bk_erase_en;
  assign req_o = rd_o | prog_o | pg_erase_o | bk_erase_o;

  logic txn_err;
  logic no_allowed_txn;
  assign no_allowed_txn = req_i & (addr_invalid | invalid_data_txn | invalid_info_txn);

  // return done and error the next cycle
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      txn_err <= 1'b0;
      err_addr_o <= '0;
    end else if (txn_err) begin
      txn_err <= 1'b0;
    end else if (no_allowed_txn) begin
      txn_err <= 1'b1;
      err_addr_o <= bank_page_addr;
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
  // Info / data errors are mutually exclusive
  `ASSERT(invalidReqOnehot_a, req_o |-> $onehot0({invalid_data_txn, invalid_info_txn}))

endmodule // flash_erase_ctrl
