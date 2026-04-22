// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Memory Protection:
// For controller requests, this module selects the right rules depending on the if_sel input and
// checks if read/write operations are permitted. In case of error, a ctrl_mp_err error will be
// returned.
// For host requests, this module will check if read operations are permitted and return an error
// if the request was not permitted.

`include "prim_assert.sv"

module rram_ctrl_mp
  import prim_mubi_pkg::mubi4_t;
  import rram_ctrl_pkg::*;
  import rram_ctrl_reg_pkg::*; (

  input logic clk_i,
  input logic rst_ni,

  input mubi4_t                   rram_disable_i,
  // Interface selection
  input rram_sel_e                if_sel_i,
  // Configuration from sw
  input mp_region_cfg_t           region_cfgs_i[TotalMpRegions],
  input mp_info_cfg_t             info_page_cfgs_i[TotalInfoPages],
  // Hardware interface override
  input  mubi4_t                  hw_info_scr_dis_i,
  input  mubi4_t                  hw_info_ecc_dis_i,
  // Interface signals to/from *_ctrl
  input  rram_phase_e             ctrl_phase_i,
  input  rram_part_e              ctrl_part_i,
  input  logic                    ctrl_rd_req_i,
  input  logic [BusAddrW-1:0]     ctrl_rd_addr_i,
  input  logic                    ctrl_rd_addr_ovfl_i,
  output logic                    ctrl_rd_done_o,
  input  logic                    ctrl_wr_req_i,
  input  logic [BusAddrW-1:0]     ctrl_wr_addr_i,
  input  logic                    ctrl_wr_addr_ovfl_i,
  output logic                    ctrl_wr_done_o,
  output logic                    ctrl_mp_err_o,
  // Interface signals to/from host adapter
  input  logic                    host_req_i,
  output logic                    host_gnt_o,
  input  logic [BusAddrW-1:0]     host_addr_i,
  output logic                    host_rd_err_o,
  output logic                    host_rd_done_o,
  output logic [BusFullWidth-1:0] host_rd_data_o,
  // Interface signals to/from rram_phy
  output logic                    ctrl_req_o,
  output logic [BusAddrW-1:0]     ctrl_addr_o,
  output logic                    ctrl_rd_o,
  output logic                    ctrl_wr_o,
  output logic                    ctrl_scramble_en_o,
  output logic                    ctrl_ecc_en_o,
  input  logic                    ctrl_rd_done_i,
  input  logic                    ctrl_wr_done_i,
  output logic                    host_req_o,
  input  logic                    host_gnt_i,
  output logic                    host_scramble_en_o,
  output logic                    host_ecc_en_o,
  input  logic                    host_rd_err_i,
  input  logic                    host_rd_done_i,
  input  logic [BusFullWidth-1:0] host_rd_data_i
);

  import prim_mubi_pkg::mubi4_test_true_strict;

  // Page address
  logic [PageW-1:0] page_addr;
  logic [PageW-1:0] end_addr;

  logic                ctrl_req;
  logic [BusAddrW-1:0] ctrl_addr;

  logic data_part_sel;
  logic info_part_sel;

  assign ctrl_req  = ctrl_rd_req_i | ctrl_wr_req_i;
  assign ctrl_addr = ctrl_rd_req_i ? ctrl_rd_addr_i : ctrl_wr_addr_i;
  assign page_addr = ctrl_addr[BusAddrW-1 -: PageW];

  assign data_part_sel = (ctrl_part_i == RramPartData);
  assign info_part_sel = (ctrl_part_i == RramPartInfo);

  ////////////////////////////////////////
  // Check address out of bounds
  // Applies for all partitions
  ////////////////////////////////////////
  logic addr_invalid;

  // Address is invalid if:
  // - The address extends beyond the end of the partition in question
  // - The address overflowed the control counters
  assign end_addr = data_part_sel ? TotalPages - 1 : TotalInfoPages - 1;

  assign addr_invalid = (ctrl_req & (page_addr > end_addr)) |
                        (ctrl_rd_req_i & ctrl_rd_addr_ovfl_i) |
                        (ctrl_wr_req_i & ctrl_wr_addr_ovfl_i);

  /////////////////////////////////
  // Check data partition access //
  /////////////////////////////////
  logic      sw_req, otp_req, lcmgr_req;
  page_cfg_t sw_sel_cfg;
  page_cfg_t hw_otp_sel_cfg;
  page_cfg_t hw_lcmgr_sel_cfg;

  assign sw_req    = ctrl_req & (if_sel_i == SwSel);
  assign otp_req   = ctrl_req & (if_sel_i == HwOtpSel);
  assign lcmgr_req = ctrl_req & (if_sel_i == HwLcMgrSel);

  rram_ctrl_mp_region_sel #(
    .Regions(TotalMpRegions)
  ) u_mp_sw_sel (
    .req_i       (sw_req),
    .phase_i     (ctrl_phase_i),
    .addr_i      (page_addr),
    .region_cfg_i(region_cfgs_i),
    .page_cfg_o  (sw_sel_cfg)
  );

  rram_ctrl_mp_region_sel #(
    .Regions(HwOtpDataRules)
  ) u_mp_hw_otp_sel (
    .req_i       (otp_req),
    .phase_i     (ctrl_phase_i),
    .addr_i      (page_addr),
    .region_cfg_i(HwOtpDataCfg[HwOtpDataRules-1:0]),
    .page_cfg_o  (hw_otp_sel_cfg)
  );

  rram_ctrl_mp_region_sel #(
    .Regions(HwLcMgrDataRules)
  ) u_mp_hw_lcmgr_sel (
    .req_i       (lcmgr_req),
    .phase_i     (ctrl_phase_i),
    .addr_i      (page_addr),
    .region_cfg_i(HwLcMgrDataCfg[HwLcMgrDataRules-1:0]),
    .page_cfg_o  (hw_lcmgr_sel_cfg)
  );

  // Select between hardware and software interfaces
  page_cfg_t data_region_cfg;
  always_comb begin
    data_region_cfg = CfgDisable;

    unique case (if_sel_i)
      HwLoopBack: data_region_cfg = CfgRw;
      SwSel:      data_region_cfg = sw_sel_cfg;
      HwOtpSel:   data_region_cfg = hw_otp_sel_cfg;
      HwLcMgrSel: data_region_cfg = hw_lcmgr_sel_cfg;
      default: ;
    endcase
  end

  logic data_en;
  logic data_rd_en, data_wr_en;
  logic data_scr_en, data_ecc_en;
  logic invalid_data_txn;

  assign data_en     = data_part_sel &
                       ~addr_invalid &
                       mubi4_test_true_strict(data_region_cfg.en);
  assign data_rd_en  = data_en & ctrl_rd_req_i & mubi4_test_true_strict(data_region_cfg.rd_en);
  assign data_wr_en  = data_en & ctrl_wr_req_i & mubi4_test_true_strict(data_region_cfg.wr_en);
  assign data_scr_en = data_en & ctrl_req & mubi4_test_true_strict(data_region_cfg.scramble_en);
  assign data_ecc_en = data_en & ctrl_req & mubi4_test_true_strict(data_region_cfg.ecc_en);

  // Check for invalid transactions
  assign invalid_data_txn = ctrl_req & data_part_sel & ~(data_rd_en | data_wr_en);

  /////////////////////////////////
  // Check info partition access //
  /////////////////////////////////
  logic [InfoPageW-1:0] info_page_addr;
  page_cfg_t            info_page_cfg_pre, hw_lcmgr_info_page_cfg, info_page_cfg;

  // rule match used for assertions only
  logic [HwLcMgrInfoRules-1:0] unused_rule_match;

  assign info_page_addr = InfoPageW'(ctrl_addr[BusAddrW-1 -: PageW]);

  // Select appropriate hw page configuration based on phase and page matching
  always_comb begin
    info_page_cfg_pre = CfgDisable;
    unused_rule_match = '0;
    if (lcmgr_req) begin
      for (int unsigned i = 0; i < HwLcMgrInfoRules; i++) begin: hw_info_region_comps
        // Select the appropriate hardware page
        if (info_page_addr == HwLcMgrInfoPageCfg[i].page &&
            ctrl_phase_i == HwLcMgrInfoPageCfg[i].phase) begin
          unused_rule_match[i] = 1'b1;
          info_page_cfg_pre = HwLcMgrInfoPageCfg[i].cfg;
        end
      end
    end

    hw_lcmgr_info_page_cfg = info_page_cfg_pre;

    // Scramble & ecc_en of info pages can be overruled
    hw_lcmgr_info_page_cfg.scramble_en = prim_mubi_pkg::mubi4_and_hi(info_page_cfg_pre.scramble_en,
                                                                     mubi4_t'(~hw_info_scr_dis_i));
    hw_lcmgr_info_page_cfg.ecc_en = prim_mubi_pkg::mubi4_and_hi(info_page_cfg_pre.ecc_en,
                                                                mubi4_t'(~hw_info_ecc_dis_i));
  end


  always_comb begin
    info_page_cfg = CfgDisable;

    unique case (if_sel_i)
      HwLoopBack: info_page_cfg = CfgRw;
      SwSel:      info_page_cfg = info_page_cfgs_i[info_page_addr].cfg;
      HwLcMgrSel: info_page_cfg = hw_lcmgr_info_page_cfg;
      default: ;
    endcase
  end

  // Page/phase fields of info_page_cfgs_i are not used.
  logic [TotalInfoPages-1:0] unused_info_page_cfg;
  for (genvar k = 0; k < TotalInfoPages; k++) begin : gen_unused_info_page
    assign unused_info_page_cfg[k] = ^{info_page_cfgs_i[k].page, info_page_cfgs_i[k].phase};
  end

  logic info_en;
  logic info_rd_en, info_wr_en;
  logic info_scr_en, info_ecc_en;
  logic invalid_info_txn;

  assign info_en     = info_part_sel &
                       ~addr_invalid &
                       mubi4_test_true_strict(info_page_cfg.en);
  assign info_rd_en  = info_en & ctrl_rd_req_i & mubi4_test_true_strict(info_page_cfg.rd_en);
  assign info_wr_en  = info_en & ctrl_wr_req_i & mubi4_test_true_strict(info_page_cfg.wr_en);
  assign info_scr_en = info_en & ctrl_req & mubi4_test_true_strict(info_page_cfg.scramble_en);
  assign info_ecc_en = info_en & ctrl_req & mubi4_test_true_strict(info_page_cfg.ecc_en);

  // Check for invalid transactions
  assign invalid_info_txn = ctrl_req & info_part_sel & ~(info_rd_en | info_wr_en);

  ////////////////////////////////////////
  // Combine all check results
  ////////////////////////////////////////
  assign ctrl_rd_o          = ctrl_req & (data_rd_en | info_rd_en);
  assign ctrl_addr_o        = ctrl_addr;
  assign ctrl_wr_o          = ctrl_req & (data_wr_en | info_wr_en);
  assign ctrl_scramble_en_o = ctrl_req & (data_scr_en | info_scr_en);
  assign ctrl_ecc_en_o      = ctrl_req & (data_ecc_en | info_ecc_en);
  assign ctrl_req_o         = ctrl_rd_o | ctrl_wr_o;

  logic txn_rd_err_d, txn_rd_err_q;
  logic txn_wr_err_d, txn_wr_err_q;
  logic no_allowed_txn;
  // If rram_disable is true, transaction is always invalid
  assign no_allowed_txn = ((prim_mubi_pkg::mubi4_test_true_loose(rram_disable_i)) ||
                           (addr_invalid | invalid_data_txn | invalid_info_txn));

  // return done and error the next cycle
  always_comb begin
    txn_rd_err_d = 1'b0;
    txn_wr_err_d = 1'b0;

    if (no_allowed_txn & ctrl_rd_req_i) begin
      txn_rd_err_d = 1'b1;
    end
    if (no_allowed_txn & ctrl_wr_req_i) begin
      txn_wr_err_d = 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      txn_rd_err_q <= 1'b0;
      txn_wr_err_q <= 1'b0;
    end else begin
      txn_rd_err_q <= txn_rd_err_d;
      txn_wr_err_q <= txn_wr_err_d;
    end
  end

  assign ctrl_rd_done_o = ctrl_rd_done_i | txn_rd_err_q;
  assign ctrl_wr_done_o = ctrl_wr_done_i | txn_wr_err_q;
  assign ctrl_mp_err_o  = txn_wr_err_q | txn_rd_err_q;

  //////////////////////////////////////////
  // Check data partition access for host //
  //////////////////////////////////////////
  logic [PageW-1:0] host_page_addr;

  page_cfg_t host_sel_cfg;
  logic      host_data_en;
  logic      host_data_rd_en;
  logic      host_data_scr_en, host_data_ecc_en;
  logic      invalid_host_txn;
  logic      err_fifo_valid, err_fifo_pop, err_fifo_req, err_fifo_rdy;
  logic      forward_err, host_mp_err;

  assign host_page_addr = host_addr_i[BusAddrW-1 -: PageW];

  rram_ctrl_mp_region_sel #(
    .Regions(TotalMpRegions)
  ) u_mp_host_sel (
    .req_i       (host_req_i),
    .phase_i     (PhaseInvalid),
    .addr_i      (host_page_addr),
    .region_cfg_i(region_cfgs_i),
    .page_cfg_o  (host_sel_cfg)
  );

  // host is a read-only interface (wr_en not used). word-offset bits not needed in MP
  logic unused_host_mp;
  assign unused_host_mp = ^{host_sel_cfg.wr_en, host_addr_i[PageW-1:0]};

  assign host_data_en     = mubi4_test_true_strict(host_sel_cfg.en);
  assign host_data_rd_en  = host_data_en & mubi4_test_true_strict(host_sel_cfg.rd_en);
  assign host_data_scr_en = host_data_en & mubi4_test_true_strict(host_sel_cfg.scramble_en);
  assign host_data_ecc_en = host_data_en & mubi4_test_true_strict(host_sel_cfg.ecc_en);

  assign invalid_host_txn = host_req_i & ((host_data_rd_en == 1'b0) ||
                                          prim_mubi_pkg::mubi4_test_true_loose(rram_disable_i));

  logic [BusFullWidth-1:0] inv_data;
  tlul_data_integ_enc u_bus_intg (
    .data_i     ({BusWidth{1'b1}}),
    .data_intg_o(inv_data)
  );

  // invalid_host_txn is stored in a FIFO to support outstanding transactions.
  assign err_fifo_req = (host_req_i & host_gnt_i) | invalid_host_txn;
  assign err_fifo_pop = host_rd_done_o;

  // This FIFO stores the error responses for outstanding requests. It is needed to return the
  // errors in the right order.
  prim_fifo_sync #(
    .Width      (1),
    .Pass       (0),
    .Depth      (NumOutstandingRdReq),
    .NeverClears(1'b1)
  ) u_err_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(err_fifo_req),
    .wready_o(err_fifo_rdy),
    .wdata_i (invalid_host_txn),
    .depth_o (),
    .full_o  (),
    .rvalid_o(err_fifo_valid),
    .rready_i(err_fifo_pop),
    .rdata_o (host_mp_err),
    .err_o   ()
  );

  // If the current response violates access rights, invalid data is output and an error is set.
  assign forward_err = host_mp_err & err_fifo_valid;

  assign host_req_o         = host_req_i & host_data_rd_en;
  assign host_gnt_o         = err_fifo_req & err_fifo_rdy;
  assign host_scramble_en_o = host_req_i & host_data_scr_en;
  assign host_ecc_en_o      = host_req_i & host_data_ecc_en;
  assign host_rd_done_o     = forward_err ? 1'b1     : host_rd_done_i;
  assign host_rd_err_o      = forward_err ? 1'b1     : host_rd_err_i;
  assign host_rd_data_o     = forward_err ? inv_data : host_rd_data_i;

  ////////////////
  // Assertions //
  ////////////////

  // Cannot match more than one info rule at a time
  `ASSERT(hwInfoRuleOnehot_A, lcmgr_req |-> $onehot0(unused_rule_match))

  // The phy cannot handle back pressure
  `ASSERT(IllegalBackPressure_A, (host_rd_done_i & forward_err) == 1'b0)

  endmodule
