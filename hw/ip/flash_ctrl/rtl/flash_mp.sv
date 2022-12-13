// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Memory Properties
//

`include "prim_assert.sv"

module flash_mp
import prim_mubi_pkg::mubi4_t;
import flash_ctrl_pkg::*;
import flash_ctrl_reg_pkg::*; (
  input clk_i,
  input rst_ni,

  input mubi4_t flash_disable_i,

  // interface selection
  input flash_sel_e if_sel_i,

  // configuration from sw
  input mp_region_cfg_t [MpRegions:0] region_cfgs_i,
  input bank_cfg_t [NumBanks-1:0] bank_cfgs_i,
  input info_page_cfg_t [NumBanks-1:0][InfoTypes-1:0][InfosPerBank-1:0] info_page_cfgs_i,
  input erase_suspend_i,
  output logic erase_suspend_done_o,

  // interface signals to/from *_ctrl
  input req_i,
  input flash_lcmgr_phase_e phase_i,
  input [AllPagesW-1:0] req_addr_i,
  input flash_part_e req_part_i,
  input [InfoTypesWidth-1:0] info_sel_i,
  input addr_ovfl_i,
  input rd_i,
  input prog_i,
  input pg_erase_i,
  input bk_erase_i,
  output logic rd_done_o,
  output logic prog_done_o,
  output logic erase_done_o,
  output logic error_o,

  // hardware interface override
  input mubi4_t hw_info_scramble_dis_i,
  input mubi4_t hw_info_ecc_dis_i,

  // interface signals to/from flash_phy
  output logic req_o,
  output logic rd_o,
  output logic prog_o,
  output logic scramble_en_o,
  output logic ecc_en_o,
  output logic he_en_o,
  output logic pg_erase_o,
  output logic bk_erase_o,
  output logic erase_suspend_o,
  input rd_done_i,
  input prog_done_i,
  input erase_done_i
);

  import prim_mubi_pkg::mubi4_test_true_strict;

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

  logic [NumBanks-1:0] bk_erase_en;
  logic data_rd_en;
  logic data_prog_en;
  logic data_pg_erase_en;
  logic data_bk_erase_en;
  logic data_scramble_en;
  logic data_ecc_en;
  logic data_he_en;
  logic info_rd_en;
  logic info_prog_en;
  logic info_pg_erase_en;
  logic info_bk_erase_en;
  logic info_scramble_en;
  logic info_ecc_en;
  logic info_he_en;

  // Memory properties handling for hardware interface
  logic hw_sel;
  assign hw_sel = if_sel_i == HwSel;

  logic data_part_sel;
  logic info_part_sel;
  assign data_part_sel = req_part_i == FlashPartData;
  assign info_part_sel = req_part_i == FlashPartInfo;


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
  assign end_addr = data_part_sel ? DataPartitionEndAddr :
                                    InfoPartitionEndAddr[info_sel_i];

  assign addr_invalid = req_i &
                        (page_addr > end_addr |
                         bank_invalid |
                         addr_ovfl_i
                        );

  ////////////////////////////////////////
  // Check data partition access
  ////////////////////////////////////////
  logic invalid_data_txn;
  data_region_attr_t sw_data_attrs [TotalRegions];
  mp_region_cfg_t sw_sel_cfg;
  mp_region_cfg_t hw_sel_cfg;

  // wrap software configurations into software attributes
  for(genvar i = 0; i < TotalRegions; i++) begin : gen_region_attrs
    assign sw_data_attrs[i].phase = PhaseInvalid;
    assign sw_data_attrs[i].cfg = region_cfgs_i[i];
  end

  flash_mp_data_region_sel #(
    .Regions(TotalRegions)
  ) u_sw_sel (
    .req_i(req_i & ~hw_sel),
    .phase_i(PhaseInvalid),
    .addr_i(bank_page_addr),
    .region_attrs_i(sw_data_attrs),
    .sel_cfg_o(sw_sel_cfg)
  );

  flash_mp_data_region_sel #(
    .Regions(HwDataRules)
  ) u_hw_sel (
    .req_i(req_i & hw_sel),
    .phase_i(phase_i),
    .addr_i(bank_page_addr),
    .region_attrs_i(HwDataAttr),
    .sel_cfg_o(hw_sel_cfg)
  );

  // select between hardware and software interfaces
  mp_region_cfg_t data_region_cfg;
  assign data_region_cfg = hw_sel ? hw_sel_cfg : sw_sel_cfg;

  // tie off unused signals
  logic [31:0] unused_region_base;
  logic [31:0] unused_region_size;
  assign unused_region_base = 32'(data_region_cfg.base);
  assign unused_region_size = 32'(data_region_cfg.size);

  // check for bank erase
  // bank erase allowed for only data partition and software interface
  always_comb begin
    for (int unsigned i = 0; i < NumBanks; i++) begin: bank_comps
      bk_erase_en[i] = (bank_addr == i[BankW-1:0]) & bank_cfgs_i[i].q & ~hw_sel;
    end
  end

  logic data_en;
  assign data_en          = data_part_sel &
                            ~addr_invalid &
                            mubi4_test_true_strict(data_region_cfg.en);

  assign data_rd_en       = data_en & rd_i &
                            mubi4_test_true_strict(data_region_cfg.rd_en);

  assign data_prog_en     = data_en & prog_i &
                            mubi4_test_true_strict(data_region_cfg.prog_en);

  assign data_pg_erase_en = data_en & pg_erase_i &
                            mubi4_test_true_strict(data_region_cfg.erase_en);

  assign data_bk_erase_en = bk_erase_i                & |bk_erase_en;

  assign data_scramble_en = data_en & (rd_i | prog_i) &
                            mubi4_test_true_strict(data_region_cfg.scramble_en);

  assign data_ecc_en      = data_en & (rd_i | prog_i) &
                            mubi4_test_true_strict(data_region_cfg.ecc_en);

  assign data_he_en       = data_en &
                            mubi4_test_true_strict(data_region_cfg.he_en);

  assign invalid_data_txn = req_i & data_part_sel &
                            ~(data_rd_en |
                              data_prog_en |
                              data_pg_erase_en |
                              data_bk_erase_en
                             );

  ////////////////////////////////////////
  // Check info partition access
  ////////////////////////////////////////

  // hardware interface permission check
  info_page_cfg_t hw_page_cfg_pre, hw_page_cfg;

  // rule match used for assertions only
  logic [HwInfoRules-1:0] unused_rule_match;

  // software interface permission check
  logic [InfoPageW-1:0] info_page_addr;
  info_page_cfg_t page_cfg;
  logic info_en;
  logic invalid_info_txn;

  // select appropriate hw page configuration based on phase and page matching
  always_comb begin
    hw_page_cfg_pre = '0;
    unused_rule_match = '0;
    if (hw_sel && req_i) begin
      for (int unsigned i = 0; i < HwInfoRules; i++) begin: hw_info_region_comps
        // select the appropriate hardware page
        if (bank_page_addr == HwInfoPageAttr[i].page.addr &&
            info_sel_i == HwInfoPageAttr[i].page.sel &&
            phase_i == HwInfoPageAttr[i].phase) begin
          unused_rule_match[i] = 1'b1;
          hw_page_cfg_pre = HwInfoPageAttr[i].cfg;
        end
      end
    end

    hw_page_cfg = hw_page_cfg_pre;
    hw_page_cfg.scramble_en = prim_mubi_pkg::mubi4_and_hi(hw_page_cfg_pre.scramble_en,
                                                          mubi4_t'(~hw_info_scramble_dis_i));
    hw_page_cfg.ecc_en = prim_mubi_pkg::mubi4_and_hi(hw_page_cfg_pre.scramble_en,
                                                     mubi4_t'(~hw_info_ecc_dis_i));
  end

  // select appropriate page configuration
  assign info_page_addr = req_addr_i[InfoPageW-1:0];
  assign page_cfg = hw_sel ? hw_page_cfg : info_page_cfgs_i[bank_addr][info_sel_i][info_page_addr];

  // final operation
  assign info_en          = info_part_sel &
                            ~addr_invalid &
                            mubi4_test_true_strict(page_cfg.en);
  assign info_rd_en       = info_en & rd_i            & mubi4_test_true_strict(page_cfg.rd_en);
  assign info_prog_en     = info_en & prog_i          & mubi4_test_true_strict(page_cfg.prog_en);
  assign info_pg_erase_en = info_en & pg_erase_i      & mubi4_test_true_strict(page_cfg.erase_en);
  // when info is selected for bank erase, the page configuration does not matter
  assign info_bk_erase_en = info_part_sel & bk_erase_i & |bk_erase_en;
  assign info_scramble_en = info_en & (rd_i | prog_i) &
                            mubi4_test_true_strict(page_cfg.scramble_en);

  assign info_ecc_en      = info_en & (rd_i | prog_i) & mubi4_test_true_strict(page_cfg.ecc_en);
  assign info_he_en       = info_en &                   mubi4_test_true_strict(page_cfg.he_en);

  // check for invalid transactions
  assign invalid_info_txn = req_i & info_part_sel &
                            ~(info_rd_en | info_prog_en | info_pg_erase_en |
                              info_bk_erase_en);


  ////////////////////////////////////////
  // Combine all check results
  ////////////////////////////////////////
  assign rd_o          = req_i & (data_rd_en | info_rd_en);
  assign prog_o        = req_i & (data_prog_en | info_prog_en);
  assign pg_erase_o    = req_i & (data_pg_erase_en | info_pg_erase_en);
  assign bk_erase_o    = req_i & (data_bk_erase_en | info_bk_erase_en);
  assign scramble_en_o = req_i & (data_scramble_en | info_scramble_en);
  assign ecc_en_o      = req_i & (data_ecc_en | info_ecc_en);
  assign he_en_o       = req_i & (data_he_en | info_he_en);
  assign req_o         = rd_o | prog_o | pg_erase_o | bk_erase_o;

  logic txn_err;
  logic no_allowed_txn;
  // if flash_disable is true, transaction is always invalid
  assign no_allowed_txn = req_i &
                           ((prim_mubi_pkg::mubi4_test_true_loose(flash_disable_i)) |
                            (addr_invalid | invalid_data_txn | invalid_info_txn));

  // return done and error the next cycle
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      txn_err <= 1'b0;
    end else if (txn_err) begin
      txn_err <= 1'b0;
    end else if (no_allowed_txn) begin
      txn_err <= 1'b1;
    end
  end

  assign rd_done_o = rd_done_i | txn_err;
  assign prog_done_o = prog_done_i | txn_err;
  assign erase_done_o = erase_done_i | txn_err;
  assign error_o = txn_err;

  // if no onigoing erase operation, immediately return
  // if ongoing erase operation, wait for flash phy return
  logic erase_valid;
  assign erase_valid = pg_erase_o | bk_erase_o;
  assign erase_suspend_o = erase_valid & erase_suspend_i;
  assign erase_suspend_done_o = erase_suspend_i & ~erase_valid |
                                erase_suspend_o & erase_done_o;


  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  //////////////////////////////////////////////

  // Bank erase enable should always be one-hot.  We cannot erase multiple banks
  // at the same time
  `ASSERT(bkEraseEnOnehot_A, (req_o & bk_erase_o) |-> $onehot(bk_erase_en))
  // Requests can only happen one at a time
  `ASSERT(requestTypesOnehot_A, req_o |-> $onehot({rd_o, prog_o, pg_erase_o, bk_erase_o}))
  // Info / data errors are mutually exclusive
  `ASSERT(invalidReqOnehot_A, req_o |-> $onehot0({invalid_data_txn, invalid_info_txn}))
  // Cannot match more than one info rule at a time
  `ASSERT(hwInfoRuleOnehot_A, req_i & hw_sel |-> $onehot0(unused_rule_match))
  // An input request should lead to an output request if there are no errors
  `ASSERT(InReqOutReq_A, req_i |-> req_o | no_allowed_txn)
  // An Info request should not lead to data requests
  `ASSERT(InfoReqToData_A, req_i & info_part_sel |-> ~|{data_en,
                                                        data_rd_en,
                                                        data_prog_en,
                                                        data_pg_erase_en})
  // A data request should not lead to info requests
  `ASSERT(DataReqToInfo_A, req_i & data_part_sel |->
    ~|{info_en,
    info_rd_en,
    info_prog_en,
    info_pg_erase_en,
    info_bk_erase_en})

  // If a bank erase request only selects data, then info should be erased
  `ASSERT(BankEraseData_A, req_i & bk_erase_i & |bk_erase_en & data_part_sel |-> data_bk_erase_en &
          ~info_bk_erase_en)

  // If a bank erase request also selects the info partition, then both data
  // and info must be erased
  `ASSERT(BankEraseInfo_A, req_i & bk_erase_i & |bk_erase_en & info_part_sel |-> &{data_bk_erase_en,
                                                                    info_bk_erase_en})

  // When no transactions are allowed, the output request should always be 0.
  `ASSERT(NoReqWhenErr_A, no_allowed_txn |-> ~req_o)


endmodule // flash_erase_ctrl
