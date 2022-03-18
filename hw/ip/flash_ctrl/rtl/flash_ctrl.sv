// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller Module
//
//

`include "prim_assert.sv"

module flash_ctrl
  import flash_ctrl_pkg::*;
  import flash_ctrl_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn    = {NumAlerts{1'b1}},
  parameter flash_key_t           RndCnstAddrKey  = RndCnstAddrKeyDefault,
  parameter flash_key_t           RndCnstDataKey  = RndCnstDataKeyDefault,
  parameter lfsr_seed_t           RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t           RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  parameter bit                   SecScrambleEn   = 1'b1
) (
  input        clk_i,
  input        rst_ni,
  input        rst_shadowed_ni,

  input        clk_otp_i,
  input        rst_otp_ni,

  // life cycle interface
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  input lc_ctrl_pkg::lc_tx_t lc_creator_seed_sw_rw_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_owner_seed_sw_rw_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_rd_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_wr_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_nvm_debug_en_i,

  // Bus Interface
  input        tlul_pkg::tl_h2d_t core_tl_i,
  output       tlul_pkg::tl_d2h_t core_tl_o,
  input        tlul_pkg::tl_h2d_t prim_tl_i,
  output       tlul_pkg::tl_d2h_t prim_tl_o,
  input        tlul_pkg::tl_h2d_t mem_tl_i,
  output       tlul_pkg::tl_d2h_t mem_tl_o,

  // otp/lc/pwrmgr/keymgr Interface
  // SEC_CM: SCRAMBLE.KEY.SIDELOAD
  output       otp_ctrl_pkg::flash_otp_key_req_t otp_o,
  input        otp_ctrl_pkg::flash_otp_key_rsp_t otp_i,
  input        lc_ctrl_pkg::lc_tx_t rma_req_i,
  input        lc_ctrl_pkg::lc_flash_rma_seed_t rma_seed_i,
  output       lc_ctrl_pkg::lc_tx_t rma_ack_o,
  output       pwrmgr_pkg::pwr_flash_t pwrmgr_o,
  output       keymgr_flash_t keymgr_o,

  // IOs
  input cio_tck_i,
  input cio_tms_i,
  input cio_tdi_i,
  output logic cio_tdo_en_o,
  output logic cio_tdo_o,

  // Interrupts
  output logic intr_corr_err_o,   // Correctable errors encountered
  output logic intr_prog_empty_o, // Program fifo is empty
  output logic intr_prog_lvl_o,   // Program fifo is empty
  output logic intr_rd_full_o,    // Read fifo is full
  output logic intr_rd_lvl_o,     // Read fifo is full
  output logic intr_op_done_o,    // Requested flash operation (wr/erase) done

  // Alerts
  input  prim_alert_pkg::alert_rx_t [flash_ctrl_reg_pkg::NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [flash_ctrl_reg_pkg::NumAlerts-1:0] alert_tx_o,

  // Observability
  input ast_pkg::ast_obs_ctrl_t obs_ctrl_i,
  output logic [7:0] fla_obs_o,

  // Flash test interface
  input scan_en_i,
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input scan_rst_ni,
  input prim_mubi_pkg::mubi4_t flash_bist_enable_i,
  input flash_power_down_h_i,
  input flash_power_ready_h_i,
  inout [1:0] flash_test_mode_a_io,
  inout flash_test_voltage_h_io,
  output ast_pkg::ast_dif_t flash_alert_o
);

  import flash_ctrl_reg_pkg::*;
  import prim_mubi_pkg::mubi4_t;

  flash_ctrl_core_reg2hw_t reg2hw;
  flash_ctrl_core_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_win_h2d [2];
  tlul_pkg::tl_d2h_t tl_win_d2h [2];

  // Register module
  logic intg_err;
  logic update_err;
  logic storage_err;

  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: CTRL.CONFIG.REGWEN
  // SEC_CM: DATA_REGIONS.CONFIG.REGWEN, DATA_REGIONS.CONFIG.SHADOW
  // SEC_CM: INFO_REGIONS.CONFIG.REGWEN, INFO_REGIONS.CONFIG.SHADOW
  // SEC_CM: BANK.CONFIG.REGWEN, BANK.CONFIG.SHADOW
  flash_ctrl_core_reg_top u_reg_core (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,

    .tl_i(core_tl_i),
    .tl_o(core_tl_o),

    .tl_win_o (tl_win_h2d),
    .tl_win_i (tl_win_d2h),

    .reg2hw,
    .hw2reg,

    .intg_err_o (intg_err),
    .devmode_i  (1'b1)
  );

  bank_cfg_t [NumBanks-1:0] bank_cfgs;
  mp_region_cfg_t [MpRegions:0] region_cfgs;
  info_page_cfg_t [NumBanks-1:0][InfoTypes-1:0][InfosPerBank-1:0] info_page_cfgs;

  flash_ctrl_region_cfg u_region_cfg (
    .clk_i,
    .rst_ni,
    .lc_creator_seed_sw_rw_en_i,
    .lc_owner_seed_sw_rw_en_i,
    .lc_iso_part_sw_wr_en_i,
    .lc_iso_part_sw_rd_en_i,
    .bank_cfg_i(reg2hw.mp_bank_cfg_shadowed),
    .region_cfg_i(reg2hw.mp_region_cfg_shadowed),
    .default_cfg_i(reg2hw.default_region_shadowed),
    .bank0_info0_cfg_i(reg2hw.bank0_info0_page_cfg_shadowed),
    .bank0_info1_cfg_i(reg2hw.bank0_info1_page_cfg_shadowed),
    .bank0_info2_cfg_i(reg2hw.bank0_info2_page_cfg_shadowed),
    .bank1_info0_cfg_i(reg2hw.bank1_info0_page_cfg_shadowed),
    .bank1_info1_cfg_i(reg2hw.bank1_info1_page_cfg_shadowed),
    .bank1_info2_cfg_i(reg2hw.bank1_info2_page_cfg_shadowed),
    .bank_cfg_o(bank_cfgs),
    .region_cfgs_o(region_cfgs),
    .info_page_cfgs_o(info_page_cfgs),
    .update_err_o(update_err),
    .storage_err_o(storage_err)
  );

  // FIFO Connections
  logic                 prog_fifo_wvalid;
  logic                 prog_fifo_wready;
  logic                 prog_fifo_rvalid;
  logic                 prog_fifo_ren;
  logic [BusWidth-1:0]  prog_fifo_wdata;
  logic [BusWidth-1:0]  prog_fifo_rdata;
  logic [FifoDepthW-1:0] prog_fifo_depth;
  logic                 rd_fifo_wready;
  logic                 rd_fifo_rvalid;
  logic                 rd_fifo_rready;
  logic                 rd_fifo_wen;
  logic                 rd_fifo_ren;
  logic [BusWidth-1:0]  rd_fifo_wdata;
  logic [BusWidth-1:0]  rd_fifo_rdata;
  logic [FifoDepthW-1:0] rd_fifo_depth;
  logic                 rd_fifo_full;

  // Program Control Connections
  logic prog_flash_req;
  logic prog_flash_ovfl;
  logic [BusAddrW-1:0] prog_flash_addr;
  logic prog_op_valid;

  // Read Control Connections
  logic rd_flash_req;
  logic rd_flash_ovfl;
  logic [BusAddrW-1:0] rd_flash_addr;
  logic rd_op_valid;

  // Erase Control Connections
  logic erase_flash_req;
  logic [BusAddrW-1:0] erase_flash_addr;
  flash_erase_e erase_flash_type;
  logic erase_op_valid;

  // Done / Error signaling from ctrl modules
  logic prog_done, rd_done, erase_done;
  flash_ctrl_err_t prog_err, rd_err, erase_err;
  logic [BusAddrW-1:0] prog_err_addr, rd_err_addr, erase_err_addr;

  // Flash Memory Properties Connections
  logic [BusAddrW-1:0] flash_addr;
  logic flash_req;
  logic flash_rd_done, flash_prog_done, flash_erase_done;
  logic flash_mp_err;
  logic [BusWidth-1:0] flash_prog_data;
  logic flash_prog_last;
  flash_prog_e flash_prog_type;
  logic [BusWidth-1:0] flash_rd_data;
  logic flash_rd_err;
  logic flash_phy_busy;
  logic rd_op;
  logic prog_op;
  logic erase_op;
  flash_lcmgr_phase_e phase;

  // Flash control arbitration connections to hardware interface
  flash_key_t addr_key;
  flash_key_t rand_addr_key;
  flash_key_t data_key;
  flash_key_t rand_data_key;
  flash_ctrl_reg2hw_control_reg_t hw_ctrl;
  logic hw_req;
  logic [BusAddrByteW-1:0] hw_addr;
  logic hw_done;
  flash_ctrl_err_t hw_err;
  logic hw_rvalid;
  logic hw_rready;
  logic hw_wvalid;
  logic [BusWidth-1:0] hw_wdata;
  logic hw_wready;
  flash_sel_e if_sel;
  logic sw_sel;
  flash_lcmgr_phase_e hw_phase;
  logic lcmgr_err;
  logic arb_fsm_err;
  logic seed_err;

  // Flash control arbitration connections to software interface
  logic sw_ctrl_done;
  flash_ctrl_err_t sw_ctrl_err;

  // Flash control muxed connections
  flash_ctrl_reg2hw_control_reg_t muxed_ctrl;
  logic [BusAddrByteW-1:0] muxed_addr;
  logic op_start;
  logic [11:0] op_num_words;
  logic [BusAddrW-1:0] op_addr;
  logic [BusAddrW-1:0] ctrl_err_addr;
  flash_op_e op_type;
  flash_part_e op_part;
  logic [InfoTypesWidth-1:0] op_info_sel;
  flash_erase_e op_erase_type;
  flash_prog_e op_prog_type;

  logic ctrl_init_busy;
  logic fifo_clr;

  // software tlul to flash control aribration
  logic sw_rvalid;
  logic adapter_rvalid;
  logic sw_wvalid;
  logic [BusWidth-1:0] sw_wdata;
  logic sw_wready;

  // lfsr for local entropy usage
  logic [31:0] rand_val;
  logic lfsr_en;
  logic lfsr_seed_en;

  // interface to flash phy
  flash_rsp_t flash_phy_rsp;
  flash_req_t flash_phy_req;

  // life cycle connections
  lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en;

  lc_ctrl_pkg::lc_tx_t dis_access;

  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_seed_hw_rd_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_seed_hw_rd_en_i),
    .lc_en_o(lc_seed_hw_rd_en)
  );

  prim_lfsr #(
    .EntropyDw(EdnWidth),
    .LfsrDw(LfsrWidth),
    .StateOutDw(LfsrWidth),
    .DefaultSeed(RndCnstLfsrSeed),
    .StatePermEn(1),
    .StatePerm(RndCnstLfsrPerm)
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .seed_en_i(lfsr_seed_en),
    .seed_i(rma_seed_i),
    .lfsr_en_i(lfsr_en),
    .entropy_i('0),
    .state_o(rand_val)
  );

  // flash control arbitration between softawre / harware interfaces
  flash_ctrl_arb u_ctrl_arb (
    .clk_i,
    .rst_ni,

    // error output shared by both interfaces
    .ctrl_err_addr_o(ctrl_err_addr),

    // software interface to rd_ctrl / erase_ctrl
    .sw_ctrl_i(reg2hw.control),
    .sw_addr_i(reg2hw.addr.q),
    .sw_ack_o(sw_ctrl_done),
    .sw_err_o(sw_ctrl_err),

    // software interface to rd_fifo
    .sw_rvalid_o(sw_rvalid),
    .sw_rready_i(adapter_rvalid),

    // software interface to prog_fifo
    // if prog operation not selected, software interface
    // writes have no meaning
    .sw_wvalid_i(sw_wvalid & prog_op_valid),
    .sw_wdata_i(sw_wdata),
    .sw_wready_o(sw_wready),

    // hardware interface to rd_ctrl / erase_ctrl
    .hw_req_i(hw_req),
    .hw_ctrl_i(hw_ctrl),

    // hardware interface indicating operation phase
    .hw_phase_i(hw_phase),

    // hardware works on word address, however software expects byte address
    .hw_addr_i(hw_addr),
    .hw_ack_o(hw_done),
    .hw_err_o(hw_err),

    // hardware interface to rd_fifo
    .hw_rvalid_o(hw_rvalid),
    .hw_rready_i(hw_rready),
    .hw_wvalid_i(hw_wvalid),
    .hw_wdata_i(hw_wdata),
    .hw_wready_o(hw_wready),

    // hardware interface does not talk to prog_fifo

    // muxed interface to rd_ctrl / erase_ctrl
    .muxed_ctrl_o(muxed_ctrl),
    .muxed_addr_o(muxed_addr),
    .prog_ack_i(prog_done),
    .prog_err_i(prog_err),
    .prog_err_addr_i(prog_err_addr),
    .rd_ack_i(rd_done),
    .rd_err_i(rd_err),
    .rd_err_addr_i(rd_err_addr),
    .erase_ack_i(erase_done),
    .erase_err_i(erase_err),
    .erase_err_addr_i(erase_err_addr),

    // muxed interface to rd_fifo
    .rd_fifo_rvalid_i(rd_fifo_rvalid),
    .rd_fifo_rready_o(rd_fifo_rready),

    // muxed interface to prog_fifo
    .prog_fifo_wvalid_o(prog_fifo_wvalid),
    .prog_fifo_wdata_o(prog_fifo_wdata),
    .prog_fifo_wready_i(prog_fifo_wready),

    // flash phy initilization ongoing
    .flash_phy_busy_i(flash_phy_busy),

    // clear fifos
    .fifo_clr_o(fifo_clr),

    // phase indication
    .phase_o(phase),

    // indication that sw has been selected
    .sel_o(if_sel),
    .fsm_err_o(arb_fsm_err)
  );

  assign op_start      = muxed_ctrl.start.q;
  assign op_num_words  = muxed_ctrl.num.q;
  assign op_erase_type = flash_erase_e'(muxed_ctrl.erase_sel.q);
  assign op_prog_type  = flash_prog_e'(muxed_ctrl.prog_sel.q);
  assign op_addr       = muxed_addr[BusByteWidth +: BusAddrW];
  assign op_type       = flash_op_e'(muxed_ctrl.op.q);
  assign op_part       = flash_part_e'(muxed_ctrl.partition_sel.q);
  assign op_info_sel   = muxed_ctrl.info_sel.q;
  assign rd_op         = op_type == FlashOpRead;
  assign prog_op       = op_type == FlashOpProgram;
  assign erase_op      = op_type == FlashOpErase;
  assign sw_sel        = if_sel == SwSel;

  // hardware interface
  flash_ctrl_lcmgr #(
    .RndCnstAddrKey(RndCnstAddrKey),
    .RndCnstDataKey(RndCnstDataKey)
  ) u_flash_hw_if (
    .clk_i,
    .rst_ni,
    .clk_otp_i,
    .rst_otp_ni,

    .init_i(reg2hw.init),
    .provision_en_i(lc_seed_hw_rd_en == lc_ctrl_pkg::On),

    // interface to ctrl arb control ports
    .ctrl_o(hw_ctrl),
    .req_o(hw_req),
    .addr_o(hw_addr),
    .done_i(hw_done),
    .err_i(hw_err),

    // interface to ctrl_arb data ports
    .rready_o(hw_rready),
    .rvalid_i(hw_rvalid),
    .wready_i(hw_wready),
    .wvalid_o(hw_wvalid),
    .wdata_o(hw_wdata),

    // direct form rd_fifo
    .rdata_i(rd_fifo_rdata),

    // external rma request
    .rma_req_i,
    .rma_ack_o,

    // outgoing seeds
    .seeds_o(keymgr_o.seeds),
    .seed_err_o(seed_err),

    // phase indication
    .phase_o(hw_phase),

    // phy read buffer enable
    .rd_buf_en_o(flash_phy_req.rd_buf_en),

    // connection to otp
    .otp_key_req_o(otp_o),
    .otp_key_rsp_i(otp_i),
    .addr_key_o(addr_key),
    .data_key_o(data_key),
    .rand_addr_key_o(rand_addr_key),
    .rand_data_key_o(rand_data_key),

    // entropy interface
    .edn_req_o(lfsr_seed_en),
    .edn_ack_i(1'b1),
    .lfsr_en_o(lfsr_en),
    .rand_i(rand_val),

    // error indication
    .fatal_err_o(lcmgr_err),

    // disable access to flash storage after rma process
    .dis_access_o(dis_access),

    // init ongoing
    .init_busy_o(ctrl_init_busy)
  );

  // Program FIFO
  // Since the program and read FIFOs are never used at the same time, it should really be one
  // FIFO with muxed inputs and outputs.  This should be addressed once the flash integration
  // strategy has been identified
  assign prog_op_valid = op_start & prog_op;

  tlul_adapter_sram #(
    .SramAw(1),         //address unused
    .SramDw(BusWidth),
    .ByteAccess(0),     //flash may not support byte access
    .ErrOnRead(1)       //reads not supported
  ) u_to_prog_fifo (
    .clk_i,
    .rst_ni,
    .tl_i        (tl_win_h2d[0]),
    .tl_o        (tl_win_d2h[0]),
    .en_ifetch_i (prim_mubi_pkg::MuBi4False),
    .req_o       (sw_wvalid),
    .req_type_o  (),
    .gnt_i       (sw_wready),
    .we_o        (),
    .addr_o      (),
    .wmask_o     (),
    .intg_error_o(),
    .wdata_o     (sw_wdata),
    .rdata_i     (BusWidth'(0)),
    .rvalid_i    (1'b0),
    .rerror_i    (2'b0)
  );

  prim_fifo_sync #(
    .Width(BusWidth),
    .Depth(FifoDepth)
  ) u_prog_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (reg2hw.fifo_rst.q | fifo_clr | sw_ctrl_done),
    .wvalid_i(prog_fifo_wvalid),
    .wready_o(prog_fifo_wready),
    .wdata_i (prog_fifo_wdata),
    .depth_o (prog_fifo_depth),
    .full_o  (),
    .rvalid_o(prog_fifo_rvalid),
    .rready_i(prog_fifo_ren),
    .rdata_o (prog_fifo_rdata)
  );

  // Program handler is consumer of prog_fifo
  logic [1:0] prog_type_en;
  assign prog_type_en[FlashProgNormal] = flash_phy_rsp.prog_type_avail[FlashProgNormal] &
                                         reg2hw.prog_type_en.normal.q;
  assign prog_type_en[FlashProgRepair] = flash_phy_rsp.prog_type_avail[FlashProgRepair] &
                                         reg2hw.prog_type_en.repair.q;

  logic prog_cnt_err;
  flash_ctrl_prog u_flash_ctrl_prog (
    .clk_i,
    .rst_ni,

    // Control interface
    .op_start_i     (prog_op_valid),
    .op_num_words_i (op_num_words),
    .op_done_o      (prog_done),
    .op_err_o       (prog_err),
    .op_addr_i      (op_addr),
    .op_addr_oob_i  ('0),
    .op_type_i      (op_prog_type),
    .type_avail_i   (prog_type_en),
    .op_err_addr_o  (prog_err_addr),
    .cnt_err_o      (prog_cnt_err),

    // FIFO Interface
    .data_i         (prog_fifo_rdata),
    .data_rdy_i     (prog_fifo_rvalid),
    .data_rd_o      (prog_fifo_ren),

    // Flash Macro Interface
    .flash_req_o    (prog_flash_req),
    .flash_addr_o   (prog_flash_addr),
    .flash_ovfl_o   (prog_flash_ovfl),
    .flash_data_o   (flash_prog_data),
    .flash_last_o   (flash_prog_last),
    .flash_type_o   (flash_prog_type),
    .flash_done_i   (flash_prog_done),
    .flash_phy_err_i(flash_phy_rsp.flash_err),
    .flash_mp_err_i (flash_mp_err)
  );

  // a read request is seen from software but a read operation is not enabled
  // AND there are no pending entries to read from the fifo.
  // This indicates software has issued a read when it should not have.
  //
  // sw_sel qualification is used here to ensure the no_op condition is ignored
  // when software is not selected through arbitration.
  logic rd_no_op_d, rd_no_op_q;
  assign rd_no_op_d = rd_fifo_ren & ~rd_op_valid & ~sw_rvalid & sw_sel;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      adapter_rvalid <= 1'b0;
      rd_no_op_q <= 1'b0;
    end else begin
      adapter_rvalid <= rd_fifo_ren & sw_rvalid;
      rd_no_op_q <= rd_no_op_d;
    end
  end

  // tlul adapter represents software's access interface to flash
  tlul_adapter_sram #(
    .SramAw(1),         //address unused
    .SramDw(BusWidth),
    .ByteAccess(0),     //flash may not support byte access
    .ErrOnWrite(1)      //writes not supported
  ) u_to_rd_fifo (
    .clk_i,
    .rst_ni,
    .tl_i        (tl_win_h2d[1]),
    .tl_o        (tl_win_d2h[1]),
    .en_ifetch_i (prim_mubi_pkg::MuBi4False),
    .req_o       (rd_fifo_ren),
    .req_type_o  (),
    // if there is no valid read operation, don't hang the
    // bus, just let things normally return
    .gnt_i       (sw_rvalid | rd_no_op_d),
    .we_o        (),
    .addr_o      (),
    .wmask_o     (),
    .wdata_o     (),
    .intg_error_o(),
    .rdata_i     (rd_fifo_rdata),
    .rvalid_i    (adapter_rvalid | rd_no_op_q),
    .rerror_i    ({rd_no_op_q, 1'b0})
  );

  prim_fifo_sync #(
    .Width(BusWidth),
    .Depth(FifoDepth)
  ) u_rd_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (reg2hw.fifo_rst.q | fifo_clr),
    .wvalid_i(rd_fifo_wen),
    .wready_o(rd_fifo_wready),
    .wdata_i (rd_fifo_wdata),
    .full_o  (rd_fifo_full),
    .depth_o (rd_fifo_depth),
    .rvalid_o(rd_fifo_rvalid),
    .rready_i(rd_fifo_rready),
    .rdata_o (rd_fifo_rdata)
  );

  logic rd_cnt_err;
  // Read handler is consumer of rd_fifo
  assign rd_op_valid = op_start & rd_op;
  flash_ctrl_rd  u_flash_ctrl_rd (
    .clk_i,
    .rst_ni,

    // To arbiter Interface
    .op_start_i     (rd_op_valid),
    .op_num_words_i (op_num_words),
    .op_done_o      (rd_done),
    .op_err_o       (rd_err),
    .op_err_addr_o  (rd_err_addr),
    .op_addr_i      (op_addr),
    .op_addr_oob_i  ('0),
    .cnt_err_o      (rd_cnt_err),

    // FIFO Interface
    .data_rdy_i     (rd_fifo_wready),
    .data_o         (rd_fifo_wdata),
    .data_wr_o      (rd_fifo_wen),

    // Flash Macro Interface
    .flash_req_o    (rd_flash_req),
    .flash_addr_o   (rd_flash_addr),
    .flash_ovfl_o   (rd_flash_ovfl),
    .flash_data_i   (flash_rd_data),
    .flash_done_i   (flash_rd_done),
    .flash_mp_err_i (flash_mp_err),
    .flash_rd_err_i (flash_rd_err),
    .flash_phy_err_i(flash_phy_rsp.flash_err)
  );

  // Erase handler does not consume fifo
  assign erase_op_valid = op_start & erase_op;
  flash_ctrl_erase u_flash_ctrl_erase (
    // Software Interface
    .op_start_i     (erase_op_valid),
    .op_type_i      (op_erase_type),
    .op_done_o      (erase_done),
    .op_err_o       (erase_err),
    .op_addr_i      (op_addr),
    .op_addr_oob_i  ('0),
    .op_err_addr_o  (erase_err_addr),

    // Flash Macro Interface
    .flash_req_o    (erase_flash_req),
    .flash_addr_o   (erase_flash_addr),
    .flash_op_o     (erase_flash_type),
    .flash_done_i   (flash_erase_done),
    .flash_mp_err_i (flash_mp_err),
    .flash_phy_err_i(flash_phy_rsp.flash_err)
  );

  // Final muxing to flash macro module
  always_comb begin
    unique case (op_type)
      FlashOpRead: begin
        flash_req = rd_flash_req;
        flash_addr = rd_flash_addr;
      end
      FlashOpProgram: begin
        flash_req = prog_flash_req;
        flash_addr = prog_flash_addr;
      end
      FlashOpErase: begin
        flash_req = erase_flash_req;
        flash_addr = erase_flash_addr;
      end
      default: begin
        flash_req = 1'b0;
        flash_addr  = '0;
      end
    endcase // unique case (op_type)
  end



  //////////////////////////////////////
  // Info partition properties configuration
  //////////////////////////////////////


  //////////////////////////////////////
  // flash memory properties
  //////////////////////////////////////
  // direct assignment since prog/rd/erase_ctrl do not make use of op_part
  flash_part_e flash_part_sel;
  logic [InfoTypesWidth-1:0] flash_info_sel;
  assign flash_part_sel = op_part;
  assign flash_info_sel = op_info_sel;

  // flash disable declaration
  prim_mubi_pkg::mubi4_t [FlashDisableLast-1:0] flash_disable;

  // tie off hardware clear path
  assign hw2reg.erase_suspend.d = 1'b0;

  // Flash memory Properties
  // Memory property is page based and thus should use phy addressing
  // This should move to flash_phy long term
  flash_mp u_flash_mp (
    .clk_i,
    .rst_ni,

    // disable flash through memory protection
    .flash_disable_i(flash_disable[MpDisableIdx]),

    // arbiter interface selection
    .if_sel_i(if_sel),

    // sw configuration for data partition
    .region_cfgs_i(region_cfgs),
    .bank_cfgs_i(bank_cfgs),

    // sw configuration for info partition
    .info_page_cfgs_i(info_page_cfgs),

    // read / prog / erase controls
    .req_i(flash_req),
    .phase_i(phase),
    .req_addr_i(flash_addr[BusAddrW-1 -: AllPagesW]),
    .req_part_i(flash_part_sel),
    .info_sel_i(flash_info_sel),
    .addr_ovfl_i(rd_flash_ovfl | prog_flash_ovfl),
    .rd_i(rd_op),
    .prog_i(prog_op),
    .pg_erase_i(erase_op & (erase_flash_type == FlashErasePage)),
    .bk_erase_i(erase_op & (erase_flash_type == FlashEraseBank)),
    .erase_suspend_i(reg2hw.erase_suspend),
    .erase_suspend_done_o(hw2reg.erase_suspend.de),
    .rd_done_o(flash_rd_done),
    .prog_done_o(flash_prog_done),
    .erase_done_o(flash_erase_done),
    .error_o(flash_mp_err),

    // flash phy interface
    .req_o(flash_phy_req.req),
    .scramble_en_o(flash_phy_req.scramble_en),
    .ecc_en_o(flash_phy_req.ecc_en),
    .he_en_o(flash_phy_req.he_en),
    .rd_o(flash_phy_req.rd),
    .prog_o(flash_phy_req.prog),
    .pg_erase_o(flash_phy_req.pg_erase),
    .bk_erase_o(flash_phy_req.bk_erase),
    .erase_suspend_o(flash_phy_req.erase_suspend),
    .rd_done_i(flash_phy_rsp.rd_done),
    .prog_done_i(flash_phy_rsp.prog_done),
    .erase_done_i(flash_phy_rsp.erase_done)
  );


  // software interface feedback
  // most values (other than flash_phy_busy) should only update when software operations
  // are actually selected
  assign hw2reg.op_status.done.d     = 1'b1;
  assign hw2reg.op_status.done.de    = sw_ctrl_done;
  assign hw2reg.op_status.err.d      = 1'b1;
  assign hw2reg.op_status.err.de     = |sw_ctrl_err;
  assign hw2reg.status.rd_full.d     = rd_fifo_full;
  assign hw2reg.status.rd_full.de    = sw_sel;
  assign hw2reg.status.rd_empty.d    = ~rd_fifo_rvalid;
  assign hw2reg.status.rd_empty.de   = sw_sel;
  assign hw2reg.status.prog_full.d   = ~prog_fifo_wready;
  assign hw2reg.status.prog_full.de  = sw_sel;
  assign hw2reg.status.prog_empty.d  = ~prog_fifo_rvalid;
  assign hw2reg.status.prog_empty.de = sw_sel;
  assign hw2reg.status.init_wip.d    = flash_phy_busy | ctrl_init_busy;
  assign hw2reg.status.init_wip.de   = 1'b1;
  assign hw2reg.control.start.d      = 1'b0;
  assign hw2reg.control.start.de     = sw_ctrl_done;
  // if software operation selected, based on transaction start
  // if software operation not selected, software is free to change contents
  assign hw2reg.ctrl_regwen.d        = sw_sel ? !op_start : 1'b1;

  // phy status
  assign hw2reg.phy_status.init_wip.d  = flash_phy_busy;
  assign hw2reg.phy_status.init_wip.de = 1'b1;
  assign hw2reg.phy_status.prog_normal_avail.d  = flash_phy_rsp.prog_type_avail[FlashProgNormal];
  assign hw2reg.phy_status.prog_normal_avail.de = 1'b1;
  assign hw2reg.phy_status.prog_repair_avail.d  = flash_phy_rsp.prog_type_avail[FlashProgRepair];
  assign hw2reg.phy_status.prog_repair_avail.de = 1'b1;

  // Flash Interface
  assign flash_phy_req.addr = flash_addr;
  assign flash_phy_req.part = flash_part_sel;
  assign flash_phy_req.info_sel = flash_info_sel;
  assign flash_phy_req.prog_type = flash_prog_type;
  assign flash_phy_req.prog_data = flash_prog_data;
  assign flash_phy_req.prog_last = flash_prog_last;
  assign flash_phy_req.region_cfgs = region_cfgs;
  assign flash_phy_req.addr_key = addr_key;
  assign flash_phy_req.data_key = data_key;
  assign flash_phy_req.rand_addr_key = rand_addr_key;
  assign flash_phy_req.rand_data_key = rand_data_key;
  assign flash_phy_req.alert_trig = reg2hw.phy_alert_cfg.alert_trig.q;
  assign flash_phy_req.alert_ack = reg2hw.phy_alert_cfg.alert_ack.q;
  assign flash_phy_req.jtag_req.tck = cio_tck_i;
  assign flash_phy_req.jtag_req.tms = cio_tms_i;
  assign flash_phy_req.jtag_req.tdi = cio_tdi_i;
  assign flash_phy_req.jtag_req.trst_n = '0;
  assign flash_phy_req.intg_err = intg_err;
  assign cio_tdo_o = flash_phy_rsp.jtag_rsp.tdo;
  assign cio_tdo_en_o = flash_phy_rsp.jtag_rsp.tdo_oe;
  assign flash_rd_err = flash_phy_rsp.rd_err;
  assign flash_rd_data = flash_phy_rsp.rd_data;
  assign flash_phy_busy = flash_phy_rsp.init_busy;


  // Interface to pwrmgr
  // flash is not idle as long as there is a stateful operation ongoing
  logic flash_idle_d;
  assign flash_idle_d = ~(flash_phy_req.req &
                          (flash_phy_req.prog | flash_phy_req.pg_erase | flash_phy_req.bk_erase));

  prim_flop #(
    .Width(1),
    .ResetValue(1'b1)
  ) u_reg_idle (
    .clk_i,
    .rst_ni,
    .d_i(flash_idle_d),
    .q_o(pwrmgr_o.flash_idle)
  );

  //////////////////////////////////////
  // Alert senders
  //////////////////////////////////////


  logic [NumAlerts-1:0] alert_srcs;
  logic [NumAlerts-1:0] alert_tests;

  // An excessive number of recoverable errors may also indicate an attack
  logic recov_err;
  assign recov_err = (sw_ctrl_done & |sw_ctrl_err) |
                     update_err;

  logic fatal_err;
  assign fatal_err = |reg2hw.fault_status;

  logic fatal_std_err;
  assign fatal_std_err = |reg2hw.std_fault_status;

  lc_ctrl_pkg::lc_tx_t local_esc;
  assign local_esc = lc_ctrl_pkg::lc_tx_bool_to_lc_tx(fatal_std_err);

  assign alert_srcs = { fatal_err,
                        fatal_std_err,
                        recov_err
                      };

  assign alert_tests = { reg2hw.alert_test.fatal_err.q & reg2hw.alert_test.fatal_err.qe,
                         reg2hw.alert_test.fatal_std_err.q & reg2hw.alert_test.fatal_std_err.qe,
                         reg2hw.alert_test.recov_err.q & reg2hw.alert_test.recov_err.qe
                       };

  localparam logic [NumAlerts-1:0] IsFatal = {1'b1, 1'b1, 1'b0};
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_senders
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(IsFatal[i])
    ) u_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_req_i(alert_srcs[i]),
      .alert_test_i(alert_tests[i]),
      .alert_ack_o(),
      .alert_state_o(),
      .alert_rx_i(alert_rx_i[i]),
      .alert_tx_o(alert_tx_o[i])
    );
  end

  //////////////////////////////////////
  // Flash Disable and execute enable
  //////////////////////////////////////

  lc_ctrl_pkg::lc_tx_t lc_escalate_en;
  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_escalation_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_escalate_en_i),
    .lc_en_o(lc_escalate_en)
  );

  lc_ctrl_pkg::lc_tx_t escalate_en;
  // SEC_CM: MEM.CTRL.LOCAL_ESC
  assign escalate_en = lc_ctrl_pkg::lc_tx_or_hi(dis_access, local_esc);

  // flash functional disable
  lc_ctrl_pkg::lc_tx_t lc_disable;
  assign lc_disable = lc_ctrl_pkg::lc_tx_or_hi(lc_escalate_en, escalate_en);

  // Normally, faults (those registered in fault_status) should also cause flash access
  // to disable.  However, most errors encountered by hardware during flash access
  // are registered as faults (since they functionally never happen).  Out of an abundance
  // of caution for the first iteration, we will not kill flash access based on those
  // faults immediately just in case there are unexpected corner conditions.
  // In other words...cowardice.
  // SEC_CM: MEM.CTRL.GLOBAL_ESC
  // SEC_CM: MEM_DISABLE.CONFIG.MUBI
  prim_mubi_pkg::mubi4_t flash_disable_pre_buf;
  assign flash_disable_pre_buf = lc_ctrl_pkg::lc_tx_test_true_loose(lc_disable) ?
                                 prim_mubi_pkg::MuBi4True :
                                 prim_mubi_pkg::mubi4_t'(reg2hw.dis.q);

  prim_mubi4_sync #(
    .NumCopies(int'(FlashDisableLast)),
    .AsyncOn(0)
  ) u_disable_buf (
    .clk_i,
    .rst_ni,
    .mubi_i(flash_disable_pre_buf),
    .mubi_o(flash_disable)
  );

  assign flash_phy_req.flash_disable = flash_disable[PhyDisableIdx];

  prim_mubi_pkg::mubi4_t sw_flash_exec_en;
  prim_mubi_pkg::mubi4_t flash_exec_en;

  // SEC_CM: MEM_EN.CONFIG.REDUN
  assign sw_flash_exec_en = (reg2hw.exec.q == unsigned'(ExecEn)) ?
                            prim_mubi_pkg::MuBi4True :
                            prim_mubi_pkg::MuBi4False;

  assign flash_exec_en = lc_ctrl_pkg::lc_tx_test_true_loose(lc_escalate_en) ?
                         prim_mubi_pkg::MuBi4False :
                         sw_flash_exec_en;


  //////////////////////////////////////
  // Errors and Interrupts
  //////////////////////////////////////

  // all software interface errors are treated as synchronous errors
  assign hw2reg.err_code.mp_err.d         = 1'b1;
  assign hw2reg.err_code.rd_err.d         = 1'b1;
  assign hw2reg.err_code.prog_win_err.d   = 1'b1;
  assign hw2reg.err_code.prog_type_err.d  = 1'b1;
  assign hw2reg.err_code.flash_phy_err.d  = 1'b1;
  assign hw2reg.err_code.update_err.d     = 1'b1;
  assign hw2reg.err_code.mp_err.de        = sw_ctrl_err.mp_err;
  assign hw2reg.err_code.rd_err.de        = sw_ctrl_err.rd_err;
  assign hw2reg.err_code.prog_win_err.de  = sw_ctrl_err.prog_win_err;
  assign hw2reg.err_code.prog_type_err.de = sw_ctrl_err.prog_type_err;
  assign hw2reg.err_code.flash_phy_err.de = sw_ctrl_err.phy_err;
  assign hw2reg.err_code.update_err.de    = update_err;
  assign hw2reg.err_addr.d                = {ctrl_err_addr, {BusByteWidth{1'h0}}};
  assign hw2reg.err_addr.de               = sw_ctrl_err.mp_err |
                                            sw_ctrl_err.rd_err |
                                            sw_ctrl_err.phy_err;

  // all hardware interface errors are considered faults
  // There are two types of faults
  // standard faults - things like fsm / counter / tlul integrity
  // custom faults - things like hardware interface not working correctly
  assign hw2reg.fault_status.mp_err.d         = 1'b1;
  assign hw2reg.fault_status.rd_err.d         = 1'b1;
  assign hw2reg.fault_status.prog_win_err.d   = 1'b1;
  assign hw2reg.fault_status.prog_type_err.d  = 1'b1;
  assign hw2reg.fault_status.flash_phy_err.d  = 1'b1;
  assign hw2reg.fault_status.seed_err.d       = 1'b1;
  assign hw2reg.fault_status.mp_err.de        = hw_err.mp_err;
  assign hw2reg.fault_status.rd_err.de        = hw_err.rd_err;
  assign hw2reg.fault_status.prog_win_err.de  = hw_err.prog_win_err;
  assign hw2reg.fault_status.prog_type_err.de = hw_err.prog_type_err;
  assign hw2reg.fault_status.flash_phy_err.de = hw_err.phy_err;
  assign hw2reg.fault_status.seed_err.de      = seed_err;

  // standard faults
  assign hw2reg.std_fault_status.reg_intg_err.d   = 1'b1;
  assign hw2reg.std_fault_status.phy_intg_err.d   = 1'b1;
  assign hw2reg.std_fault_status.lcmgr_err.d      = 1'b1;
  assign hw2reg.std_fault_status.arb_fsm_err.d    = 1'b1;
  assign hw2reg.std_fault_status.storage_err.d    = 1'b1;
  assign hw2reg.std_fault_status.phy_fsm_err.d    = 1'b1;
  assign hw2reg.std_fault_status.ctrl_cnt_err.d   = 1'b1;
  assign hw2reg.std_fault_status.reg_intg_err.de  = intg_err;
  assign hw2reg.std_fault_status.phy_intg_err.de  = flash_phy_rsp.intg_err;
  assign hw2reg.std_fault_status.lcmgr_err.de     = lcmgr_err;
  assign hw2reg.std_fault_status.arb_fsm_err.de   = arb_fsm_err;
  assign hw2reg.std_fault_status.storage_err.de   = storage_err;
  assign hw2reg.std_fault_status.phy_fsm_err.de   = flash_phy_rsp.fsm_err;
  assign hw2reg.std_fault_status.ctrl_cnt_err.de  = rd_cnt_err | prog_cnt_err;

  // Correctable ECC count / address
  for (genvar i = 0; i < NumBanks; i++) begin : gen_ecc_single_err_reg
    assign hw2reg.ecc_single_err_cnt[i].de = flash_phy_rsp.ecc_single_err[i];
    assign hw2reg.ecc_single_err_cnt[i].d = &reg2hw.ecc_single_err_cnt[i].q ?
                                            reg2hw.ecc_single_err_cnt[i].q :
                                            reg2hw.ecc_single_err_cnt[i].q + 1'b1;

    assign hw2reg.ecc_single_err_addr[i].de = flash_phy_rsp.ecc_single_err[i];
    assign hw2reg.ecc_single_err_addr[i].d = {flash_phy_rsp.ecc_addr[i], {BusByteWidth{1'b0}}};
  end

  // general interrupt events
  logic [LastIntrIdx-1:0] intr_event;

  prim_edge_detector #(
    .Width(1),
    .ResetValue(1)
  ) u_prog_empty_event (
    .clk_i,
    .rst_ni,
    .d_i(~prog_fifo_rvalid),
    .q_sync_o(),
    .q_posedge_pulse_o(intr_event[ProgEmpty]),
    .q_negedge_pulse_o()
  );

  prim_intr_hw #(.Width(1)) u_intr_prog_empty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_event[ProgEmpty]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.prog_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.prog_empty.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.prog_empty.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.prog_empty.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.prog_empty.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.prog_empty.d),
    .intr_o                 (intr_prog_empty_o)
  );

  prim_edge_detector #(
    .Width(1),
    .ResetValue(0)
  ) u_prog_lvl_event (
    .clk_i,
    .rst_ni,
    .d_i(reg2hw.fifo_lvl.prog.q == prog_fifo_depth),
    .q_sync_o(),
    .q_posedge_pulse_o(intr_event[ProgLvl]),
    .q_negedge_pulse_o()
  );

  prim_intr_hw #(.Width(1)) u_intr_prog_lvl (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_event[ProgLvl]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.prog_lvl.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.prog_lvl.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.prog_lvl.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.prog_lvl.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.prog_lvl.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.prog_lvl.d),
    .intr_o                 (intr_prog_lvl_o)
  );

  prim_edge_detector #(
    .Width(1),
    .ResetValue(0)
  ) u_rd_full_event (
    .clk_i,
    .rst_ni,
    .d_i(rd_fifo_full),
    .q_sync_o(),
    .q_posedge_pulse_o(intr_event[RdFull]),
    .q_negedge_pulse_o()
  );

  prim_intr_hw #(.Width(1)) u_intr_rd_full (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_event[RdFull]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rd_full.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rd_full.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rd_full.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rd_full.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rd_full.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rd_full.d),
    .intr_o                 (intr_rd_full_o)
  );

  prim_edge_detector #(
    .Width(1),
    .ResetValue(0)
  ) u_rd_lvl_event (
    .clk_i,
    .rst_ni,
    .d_i(reg2hw.fifo_lvl.rd.q == rd_fifo_depth),
    .q_sync_o(),
    .q_posedge_pulse_o(intr_event[RdLvl]),
    .q_negedge_pulse_o()
  );

  prim_intr_hw #(.Width(1)) u_intr_rd_lvl (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_event[RdLvl]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rd_lvl.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rd_lvl.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rd_lvl.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rd_lvl.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rd_lvl.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rd_lvl.d),
    .intr_o                 (intr_rd_lvl_o)
  );

  assign intr_event[OpDone] = sw_ctrl_done;
  assign intr_event[CorrErr] = |flash_phy_rsp.ecc_single_err;

  prim_intr_hw #(.Width(1)) u_intr_op_done (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_event[OpDone]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.op_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.op_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.op_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.op_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.op_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.op_done.d),
    .intr_o                 (intr_op_done_o)
  );

  prim_intr_hw #(.Width(1)) u_intr_corr_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_event[CorrErr]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.corr_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.corr_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.corr_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.corr_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.corr_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.corr_err.d),
    .intr_o                 (intr_corr_err_o)
  );

  // Unused bits
  logic [BusByteWidth-1:0] unused_byte_sel;
  logic [top_pkg::TL_AW-1:0] unused_scratch;

  // Unused signals
  assign unused_byte_sel = muxed_addr[BusByteWidth-1:0];
  assign unused_scratch = reg2hw.scratch;


  //////////////////////////////////////
  // flash phy module
  //////////////////////////////////////
  logic flash_host_req;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic flash_host_rderr;
  logic [flash_ctrl_pkg::BusWidth-1:0] flash_host_rdata;
  logic [flash_ctrl_pkg::BusAddrW-1:0] flash_host_addr;
  logic flash_host_intg_err;

  import prim_mubi_pkg::mubi4_test_true_loose;
  logic host_disable;
  logic disabled_rvalid;
  logic [1:0] disabled_err;

  // if flash disable is activated, error back from the adapter interface immediately
  assign host_disable = mubi4_test_true_loose(flash_disable[HostDisableIdx]);
  assign disabled_err = {2{disabled_rvalid}};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      disabled_rvalid <= '0;
    end else begin
      disabled_rvalid <= host_disable & flash_host_req;
    end
  end

  tlul_adapter_sram #(
    .SramAw(BusAddrW),
    .SramDw(BusWidth),
    .Outstanding(2),
    .ByteAccess(0),
    .ErrOnWrite(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(1)
  ) u_tl_adapter_eflash (
    .clk_i,
    .rst_ni,
    .tl_i        (mem_tl_i),
    .tl_o        (mem_tl_o),
    .en_ifetch_i (flash_exec_en),
    .req_o       (flash_host_req),
    .req_type_o  (),
    .gnt_i       (flash_host_req_rdy | host_disable),
    .we_o        (),
    .addr_o      (flash_host_addr),
    .wdata_o     (),
    .wmask_o     (),
    .intg_error_o(flash_host_intg_err),
    .rdata_i     (flash_host_rdata),
    .rvalid_i    (flash_host_req_done | disabled_rvalid),
    .rerror_i    ({flash_host_rderr,1'b0} | disabled_err)
  );

  flash_phy #(
    .SecScrambleEn(SecScrambleEn)
  ) u_eflash (
    .clk_i,
    .rst_ni,
    .host_req_i        (flash_host_req),
    .host_intg_err_i   (flash_host_intg_err),
    .host_addr_i       (flash_host_addr),
    .host_req_rdy_o    (flash_host_req_rdy),
    .host_req_done_o   (flash_host_req_done),
    .host_rderr_o      (flash_host_rderr),
    .host_rdata_o      (flash_host_rdata),
    .flash_ctrl_i      (flash_phy_req),
    .flash_ctrl_o      (flash_phy_rsp),
    .tl_i              (prim_tl_i),
    .tl_o              (prim_tl_o),
    .obs_ctrl_i,
    .fla_obs_o,
    .lc_nvm_debug_en_i,
    .flash_bist_enable_i,
    .flash_power_down_h_i,
    .flash_power_ready_h_i,
    .flash_test_mode_a_io,
    .flash_test_voltage_h_io,
    .flash_alert_o,
    .scanmode_i,
    .scan_en_i,
    .scan_rst_ni
  );

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A,       core_tl_o.d_valid )
  `ASSERT_KNOWN(TlAReadyKnownO_A,       core_tl_o.a_ready )
  `ASSERT_KNOWN_IF(RspPayLoad_A,        core_tl_o, core_tl_o.d_valid)
  `ASSERT_KNOWN(PrimTlDValidKnownO_A,   prim_tl_o.d_valid )
  `ASSERT_KNOWN(PrimTlAReadyKnownO_A,   prim_tl_o.a_ready )
  `ASSERT_KNOWN_IF(PrimRspPayLoad_A,    prim_tl_o, prim_tl_o.d_valid)
  `ASSERT_KNOWN(MemTlDValidKnownO_A,    mem_tl_o.d_valid )
  `ASSERT_KNOWN(MemTlAReadyKnownO_A,    mem_tl_o.a_ready )
  `ASSERT_KNOWN_IF(MemRspPayLoad_A,     mem_tl_o, mem_tl_o.d_valid)
  `ASSERT_KNOWN(FlashKnownO_A,          {flash_phy_req.req, flash_phy_req.rd,
                                         flash_phy_req.prog, flash_phy_req.pg_erase,
                                         flash_phy_req.bk_erase})
  `ASSERT_KNOWN_IF(FlashAddrKnown_A,    flash_phy_req.addr, flash_phy_req.req)
  `ASSERT_KNOWN_IF(FlashProgKnown_A,    flash_phy_req.prog_data,
    flash_phy_req.prog & flash_phy_req.req)
  `ASSERT_KNOWN(IntrProgEmptyKnownO_A,  intr_prog_empty_o)
  `ASSERT_KNOWN(IntrProgLvlKnownO_A,    intr_prog_lvl_o  )
  `ASSERT_KNOWN(IntrProgRdFullKnownO_A, intr_rd_full_o   )
  `ASSERT_KNOWN(IntrRdLvlKnownO_A,      intr_rd_lvl_o    )
  `ASSERT_KNOWN(IntrOpDoneKnownO_A,     intr_op_done_o   )
  `ASSERT_KNOWN(IntrErrO_A,             intr_corr_err_o  )

  // combined indication that an operation has started
  // This is used only for assertions
  logic unused_op_valid;
  assign unused_op_valid = prog_op_valid | rd_op_valid | erase_op_valid;

  // add more assertions
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PageCntAlertCheck_A, u_flash_hw_if.u_page_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(WordCntAlertCheck_A, u_flash_hw_if.u_word_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(WipeIdx_A, u_flash_hw_if.u_wipe_idx_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(ProgCnt_A, u_flash_ctrl_prog.u_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(RdCnt_A, u_flash_ctrl_rd.u_cnt,
                                         alert_tx_o[1])

  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(LcCtrlFsmCheck_A,
    u_flash_hw_if.u_state_regs, alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(LcCtrlRmaFsmCheck_A,
    u_flash_hw_if.u_rma_state_regs, alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(ArbFsmCheck_A,
    u_ctrl_arb.u_state_regs, alert_tx_o[1])

   for (genvar i=0; i<NumBanks; i++) begin : gen_phy_assertions
     `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(PhyFsmCheck_A,
       u_eflash.gen_flash_cores[i].u_core.u_state_regs, alert_tx_o[1])

     `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(PhyProgFsmCheck_A,
       u_eflash.gen_flash_cores[i].u_core.gen_prog_data.u_prog.u_state_regs, alert_tx_o[1])
   end

endmodule
