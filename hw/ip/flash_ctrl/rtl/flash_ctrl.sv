// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller Module
//
//

`include "prim_assert.sv"

module flash_ctrl
  import flash_ctrl_pkg::*;  import flash_ctrl_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn    = {NumAlerts{1'b1}},
  parameter flash_key_t           RndCnstAddrKey  = RndCnstAddrKeyDefault,
  parameter flash_key_t           RndCnstDataKey  = RndCnstDataKeyDefault,
  parameter all_seeds_t           RndCnstAllSeeds = RndCnstAllSeedsDefault,
  parameter lfsr_seed_t           RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t           RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  parameter int                   ProgFifoDepth   = MaxFifoDepth,
  parameter int                   RdFifoDepth     = MaxFifoDepth,
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
  inout flash_test_voltage_h_io
);

  //////////////////////////////////////////////////////////
  // Double check supplied param is not bigger than allowed
  //////////////////////////////////////////////////////////
  `ASSERT_INIT(FifoDepthCheck_A, (ProgFifoDepth <= MaxFifoDepth) &
                                 (RdFifoDepth <= MaxFifoDepth))


  import flash_ctrl_reg_pkg::*;
  import prim_mubi_pkg::mubi4_t;

  flash_ctrl_core_reg2hw_t reg2hw;
  flash_ctrl_core_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_win_h2d [2];
  tlul_pkg::tl_d2h_t tl_win_d2h [2];

  // Register module
  logic storage_err;
  logic update_err;
  logic intg_err;
  logic eflash_cmd_intg_err;
  logic tl_gate_intg_err;
  logic tl_prog_gate_intg_err;

  // SEC_CM: REG.BUS.INTEGRITY
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

    .shadowed_storage_err_o (storage_err),
    .shadowed_update_err_o  (update_err),
    .intg_err_o             (intg_err),

    .devmode_i (1'b1)
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
    .region_i(reg2hw.mp_region),
    .region_cfg_i(reg2hw.mp_region_cfg),
    .default_cfg_i(reg2hw.default_region),
    .bank0_info0_cfg_i(reg2hw.bank0_info0_page_cfg),
    .bank0_info1_cfg_i(reg2hw.bank0_info1_page_cfg),
    .bank0_info2_cfg_i(reg2hw.bank0_info2_page_cfg),
    .bank1_info0_cfg_i(reg2hw.bank1_info0_page_cfg),
    .bank1_info1_cfg_i(reg2hw.bank1_info1_page_cfg),
    .bank1_info2_cfg_i(reg2hw.bank1_info2_page_cfg),
    .bank_cfg_o(bank_cfgs),
    .region_cfgs_o(region_cfgs),
    .info_page_cfgs_o(info_page_cfgs)
  );

  // FIFO Connections
  localparam int ProgDepthW = prim_util_pkg::vbits(ProgFifoDepth+1);
  localparam int RdDepthW   = prim_util_pkg::vbits(RdFifoDepth+1);

  logic                    prog_fifo_wvalid;
  logic                    prog_fifo_wready;
  logic                    prog_fifo_rvalid;
  logic                    prog_fifo_ren;
  logic [BusFullWidth-1:0] prog_fifo_wdata;
  logic [BusFullWidth-1:0] prog_fifo_rdata;
  logic [ProgDepthW-1:0]   prog_fifo_depth;

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
  logic                    rd_ctrl_wen;
  logic [BusFullWidth-1:0] rd_ctrl_wdata;


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
  logic [BusFullWidth-1:0] flash_prog_data;
  logic flash_prog_last;
  flash_prog_e flash_prog_type;
  logic [BusFullWidth-1:0] flash_rd_data;
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
  logic hw_wvalid;
  logic [BusFullWidth-1:0] hw_wdata;
  logic hw_wready;
  flash_sel_e if_sel;
  logic sw_sel;
  flash_lcmgr_phase_e hw_phase;
  logic lcmgr_err;
  logic lcmgr_intg_err;
  logic arb_fsm_err;
  logic seed_err;

  // Flash lcmgr interface to direct read fifo
  logic lcmgr_rready;

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
  logic ctrl_initialized;
  logic fifo_clr;

  // sw read fifo interface
  logic sw_rfifo_wen;
  logic sw_rfifo_wready;
  logic [BusFullWidth-1:0] sw_rfifo_wdata;
  logic sw_rfifo_full;
  logic [RdDepthW-1:0] sw_rfifo_depth;
  logic sw_rfifo_rvalid;
  logic sw_rfifo_rready;
  logic [BusFullWidth-1:0] sw_rfifo_rdata;

  // software tlul interface to read fifo
  logic adapter_req;
  logic adapter_rvalid;
  logic adapter_fifo_err;

  // software tlul interface to prog fifo
  logic sw_wvalid;
  logic [BusFullWidth-1:0] sw_wdata;
  logic sw_wready;

  // lfsr for local entropy usage
  logic [31:0] rand_val;
  logic lfsr_en;
  logic lfsr_seed_en;

  // interface to flash phy
  flash_rsp_t flash_phy_rsp;
  flash_req_t flash_phy_req;

  // import commonly used routines
  import lc_ctrl_pkg::lc_tx_test_true_strict;

  // life cycle connections
  lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en;

  lc_ctrl_pkg::lc_tx_t dis_access;

  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_seed_hw_rd_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_seed_hw_rd_en_i),
    .lc_en_o({lc_seed_hw_rd_en})
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

  // flash disable declaration
  mubi4_t [FlashDisableLast-1:0] flash_disable;

  // flash control arbitration between software and hardware interfaces
  flash_ctrl_arb u_ctrl_arb (
    .clk_i,
    .rst_ni,

    // combined disable
    .disable_i(flash_disable[ArbFsmDisableIdx]),

    // error output shared by both interfaces
    .ctrl_err_addr_o(ctrl_err_addr),

    // software interface to rd_ctrl / erase_ctrl
    .sw_ctrl_i(reg2hw.control),
    .sw_addr_i(reg2hw.addr.q),
    .sw_ack_o(sw_ctrl_done),
    .sw_err_o(sw_ctrl_err),

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
    .RndCnstDataKey(RndCnstDataKey),
    .RndCnstAllSeeds(RndCnstAllSeeds)
  ) u_flash_hw_if (
    .clk_i,
    .rst_ni,
    .clk_otp_i,
    .rst_otp_ni,

    .init_i(reg2hw.init),
    .provision_en_i(lc_tx_test_true_strict(lc_seed_hw_rd_en)),

    // combined disable
    .disable_i(flash_disable[LcMgrDisableIdx]),

    // interface to ctrl arb control ports
    .ctrl_o(hw_ctrl),
    .req_o(hw_req),
    .addr_o(hw_addr),
    .done_i(hw_done),
    .err_i(hw_err),

    // interface to ctrl_arb data ports
    .wready_i(hw_wready),
    .wvalid_o(hw_wvalid),
    .wdata_o(hw_wdata),

    // interface to hw interface read fifo
    .rready_o(lcmgr_rready),
    .rvalid_i(~sw_sel & rd_ctrl_wen),
    .rdata_i(rd_ctrl_wdata),

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
    .intg_err_o(lcmgr_intg_err),

    // disable access to flash storage after rma process
    .dis_access_o(dis_access),

    // init ongoing
    .init_busy_o(ctrl_init_busy),
    .initialized_o(ctrl_initialized),

    .debug_state_o(hw2reg.debug_state.d)
  );




  // Program FIFO
  // Since the program and read FIFOs are never used at the same time, it should really be one
  // FIFO with muxed inputs and outputs.  This should be addressed once the flash integration
  // strategy has been identified
  assign prog_op_valid = op_start & prog_op;

  tlul_pkg::tl_h2d_t prog_tl_h2d;
  tlul_pkg::tl_d2h_t prog_tl_d2h;

  // the program path also needs an lc gate to error back when flash is disabled.
  // This is because tlul_adapter_sram does not actually have a way of signaling
  // write errors, only read errors.
  // SEC_CM: PROG_TL_LC_GATE.FSM.SPARSE
  tlul_lc_gate u_prog_tl_gate (
    .clk_i,
    .rst_ni,
    .tl_h2d_i(tl_win_h2d[0]),
    .tl_d2h_o(tl_win_d2h[0]),
    .tl_h2d_o(prog_tl_h2d),
    .tl_d2h_i(prog_tl_d2h),
    .flush_req_i('0),
    .flush_ack_o(),
    .resp_pending_o(),
    .lc_en_i(lc_ctrl_pkg::mubi4_to_lc_inv(flash_disable[ProgFifoIdx])),
    .err_o(tl_prog_gate_intg_err)
  );

  tlul_adapter_sram #(
    .SramAw(1),          //address unused
    .SramDw(BusWidth),
    .ByteAccess(0),      //flash may not support byte access
    .ErrOnRead(1),       //reads not supported
    .EnableDataIntgPt(1) //passthrough data integrity
  ) u_to_prog_fifo (
    .clk_i,
    .rst_ni,
    .tl_i        (prog_tl_h2d),
    .tl_o        (prog_tl_d2h),
    .en_ifetch_i (prim_mubi_pkg::MuBi4False),
    .req_o       (sw_wvalid),
    .req_type_o  (),
    .gnt_i       (sw_wready),
    .we_o        (),
    .addr_o      (),
    .wmask_o     (),
    .intg_error_o(),
    .wdata_o     (sw_wdata),
    .rdata_i     ('0),
    .rvalid_i    (1'b0),
    .rerror_i    (2'b0)
  );

  prim_fifo_sync #(
    .Width(BusFullWidth),
    .Depth(ProgFifoDepth)
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
    .rdata_o (prog_fifo_rdata),
    .err_o   ()
  );
  assign hw2reg.curr_fifo_lvl.prog.d = MaxFifoWidth'(prog_fifo_depth);

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
    .flash_prog_intg_err_i (flash_phy_rsp.prog_intg_err),
    .flash_mp_err_i (flash_mp_err)
  );



  // a read request is seen from software but a read operation is not enabled
  // AND there are no pending entries to read from the fifo.
  // This indicates software has issued a read when it should not have.
  logic rd_no_op_d, rd_no_op_q;
  logic sw_rd_op;
  assign sw_rd_op = reg2hw.control.start.q & (reg2hw.control.op.q == FlashOpRead);

  // If software ever attempts to read when the FIFO is empty AND if it has never
  // initiated a transaction, OR when flash is disabled, then it is a read that
  // can never complete, error back immediately.
  assign rd_no_op_d = adapter_req & ((~sw_rd_op & ~sw_rfifo_rvalid) |
                      (prim_mubi_pkg::mubi4_test_true_loose(flash_disable[RdFifoIdx])));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      adapter_rvalid <= 1'b0;
      rd_no_op_q <= 1'b0;
    end else begin
      adapter_rvalid <= adapter_req & sw_rfifo_rvalid;
      rd_no_op_q <= rd_no_op_d;
    end
  end

  // tlul adapter represents software's access interface to flash
  tlul_adapter_sram #(
    .SramAw(1),           //address unused
    .SramDw(BusWidth),
    .ByteAccess(0),       //flash may not support byte access
    .ErrOnWrite(1),       //writes not supported
    .EnableDataIntgPt(1),
    .SecFifoPtr(1)        // SEC_CM: FIFO.CTR.REDUN
  ) u_to_rd_fifo (
    .clk_i,
    .rst_ni,
    .tl_i        (tl_win_h2d[1]),
    .tl_o        (tl_win_d2h[1]),
    .en_ifetch_i (prim_mubi_pkg::MuBi4False),
    .req_o       (adapter_req),
    .req_type_o  (),
    // if there is no valid read operation, don't hang the
    // bus, just let things normally return
    .gnt_i       (sw_rfifo_rvalid | rd_no_op_d),
    .we_o        (),
    .addr_o      (),
    .wmask_o     (),
    .wdata_o     (),
    .intg_error_o(adapter_fifo_err),
    .rdata_i     (sw_rfifo_rdata),
    .rvalid_i    (adapter_rvalid | rd_no_op_q),
    .rerror_i    ({rd_no_op_q, 1'b0})
  );

  assign sw_rfifo_wen = sw_sel & rd_ctrl_wen;
  assign sw_rfifo_wdata = rd_ctrl_wdata;
  assign sw_rfifo_rready = adapter_rvalid;

  // the read fifo below is dedicated to the software read path.
  prim_fifo_sync #(
    .Width(BusFullWidth),
    .Depth(RdFifoDepth)
  ) u_sw_rd_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (reg2hw.fifo_rst.q),
    .wvalid_i(sw_rfifo_wen),
    .wready_o(sw_rfifo_wready),
    .wdata_i (sw_rfifo_wdata),
    .full_o  (sw_rfifo_full),
    .depth_o (sw_rfifo_depth),
    .rvalid_o(sw_rfifo_rvalid),
    .rready_i(sw_rfifo_rready),
    .rdata_o (sw_rfifo_rdata),
    .err_o   ()
  );
  assign hw2reg.curr_fifo_lvl.rd.d = sw_rfifo_depth;

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
    .data_rdy_i     (sw_sel ? sw_rfifo_wready : lcmgr_rready),
    .data_o         (rd_ctrl_wdata),
    .data_wr_o      (rd_ctrl_wen),

    // Flash Macro Interface
    .flash_req_o    (rd_flash_req),
    .flash_addr_o   (rd_flash_addr),
    .flash_ovfl_o   (rd_flash_ovfl),
    .flash_data_i   (flash_rd_data),
    .flash_done_i   (flash_rd_done),
    .flash_mp_err_i (flash_mp_err),
    .flash_rd_err_i (flash_rd_err)
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
    .flash_mp_err_i (flash_mp_err)
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

    // hw info configuration overrides
    .hw_info_scramble_dis_i(mubi4_t'(reg2hw.hw_info_cfg_override.scramble_dis.q)),
    .hw_info_ecc_dis_i(mubi4_t'(reg2hw.hw_info_cfg_override.ecc_dis.q)),

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
  assign hw2reg.status.rd_full.d     = sw_rfifo_full;
  assign hw2reg.status.rd_full.de    = sw_sel;
  assign hw2reg.status.rd_empty.d    = ~sw_rfifo_rvalid;
  assign hw2reg.status.rd_empty.de   = sw_sel;
  assign hw2reg.status.prog_full.d   = ~prog_fifo_wready;
  assign hw2reg.status.prog_full.de  = sw_sel;
  assign hw2reg.status.prog_empty.d  = ~prog_fifo_rvalid;
  assign hw2reg.status.prog_empty.de = sw_sel;
  assign hw2reg.status.init_wip.d    = flash_phy_busy | ctrl_init_busy;
  assign hw2reg.status.init_wip.de   = 1'b1;
  assign hw2reg.status.initialized.d  = ctrl_initialized & ~flash_phy_busy;
  assign hw2reg.status.initialized.de = 1'b1;
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
  logic fatal_prim_flash_alert, recov_prim_flash_alert;

  // An excessive number of recoverable errors may also indicate an attack
  logic recov_err;
  assign recov_err = (sw_ctrl_done & |sw_ctrl_err) |
                     flash_phy_rsp.macro_err |
                     update_err;

  logic fatal_err;
  assign fatal_err = |reg2hw.fault_status;

  logic fatal_std_err;
  assign fatal_std_err = |reg2hw.std_fault_status;

  lc_ctrl_pkg::lc_tx_t local_esc;
  assign local_esc = lc_ctrl_pkg::lc_tx_bool_to_lc_tx(fatal_std_err);

  assign alert_srcs = {
    recov_prim_flash_alert,
    fatal_prim_flash_alert,
    fatal_err,
    fatal_std_err,
    recov_err
  };

  assign alert_tests = {
    reg2hw.alert_test.recov_prim_flash_alert.q & reg2hw.alert_test.recov_prim_flash_alert.qe,
    reg2hw.alert_test.fatal_prim_flash_alert.q & reg2hw.alert_test.fatal_prim_flash_alert.qe,
    reg2hw.alert_test.fatal_err.q & reg2hw.alert_test.fatal_err.qe,
    reg2hw.alert_test.fatal_std_err.q & reg2hw.alert_test.fatal_std_err.qe,
    reg2hw.alert_test.recov_err.q & reg2hw.alert_test.recov_err.qe
  };

  localparam logic [NumAlerts-1:0] IsFatal = {1'b0, 1'b1, 1'b1, 1'b1, 1'b0};
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
    .lc_en_o({lc_escalate_en})
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
  mubi4_t lc_conv_disable;
  mubi4_t flash_disable_pre_buf;
  assign lc_conv_disable = lc_ctrl_pkg::lc_to_mubi4(lc_disable);
  assign flash_disable_pre_buf = prim_mubi_pkg::mubi4_or_hi(
      lc_conv_disable,
      mubi4_t'(reg2hw.dis.q));

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

  logic [prim_mubi_pkg::MuBi4Width-1:0] sw_flash_exec_en;
  mubi4_t flash_exec_en;

  // SEC_CM: EXEC.CONFIG.REDUN
  prim_sec_anchor_buf #(
    .Width(prim_mubi_pkg::MuBi4Width)
  ) u_exec_en_buf (
    .in_i(prim_mubi_pkg::mubi4_bool_to_mubi(reg2hw.exec.q == unsigned'(ExecEn))),
    .out_o(sw_flash_exec_en)
  );

  mubi4_t disable_exec;
  assign disable_exec = mubi4_t'(~flash_disable[IFetchDisableIdx]);
  assign flash_exec_en = prim_mubi_pkg::mubi4_and_hi(
                           disable_exec,
                           mubi4_t'(sw_flash_exec_en)
                         );

  //////////////////////////////////////
  // Errors and Interrupts
  //////////////////////////////////////

  // all software interface errors are treated as synchronous errors
  assign hw2reg.err_code.op_err.d           = 1'b1;
  assign hw2reg.err_code.mp_err.d           = 1'b1;
  assign hw2reg.err_code.rd_err.d           = 1'b1;
  assign hw2reg.err_code.prog_err.d         = 1'b1;
  assign hw2reg.err_code.prog_win_err.d     = 1'b1;
  assign hw2reg.err_code.prog_type_err.d    = 1'b1;
  assign hw2reg.err_code.update_err.d       = 1'b1;
  assign hw2reg.err_code.macro_err.d        = 1'b1;
  assign hw2reg.err_code.op_err.de          = sw_ctrl_err.invalid_op_err;
  assign hw2reg.err_code.mp_err.de          = sw_ctrl_err.mp_err;
  assign hw2reg.err_code.rd_err.de          = sw_ctrl_err.rd_err;
  assign hw2reg.err_code.prog_err.de        = sw_ctrl_err.prog_err;
  assign hw2reg.err_code.prog_win_err.de    = sw_ctrl_err.prog_win_err;
  assign hw2reg.err_code.prog_type_err.de   = sw_ctrl_err.prog_type_err;
  assign hw2reg.err_code.update_err.de      = update_err;
  assign hw2reg.err_code.macro_err.de       = flash_phy_rsp.macro_err;
  assign hw2reg.err_addr.d                  = {ctrl_err_addr, {BusByteWidth{1'h0}}};
  assign hw2reg.err_addr.de                 = sw_ctrl_err.mp_err |
                                              sw_ctrl_err.rd_err |
                                              sw_ctrl_err.prog_err;


  // all hardware interface errors are considered faults
  // There are two types of faults
  // standard faults - things like fsm / counter / tlul integrity
  // custom faults - things like hardware interface not working correctly
  assign hw2reg.fault_status.op_err.d           = 1'b1;
  assign hw2reg.fault_status.mp_err.d           = 1'b1;
  assign hw2reg.fault_status.rd_err.d           = 1'b1;
  assign hw2reg.fault_status.prog_err.d         = 1'b1;
  assign hw2reg.fault_status.prog_win_err.d     = 1'b1;
  assign hw2reg.fault_status.prog_type_err.d    = 1'b1;
  assign hw2reg.fault_status.seed_err.d         = 1'b1;
  assign hw2reg.fault_status.phy_relbl_err.d    = 1'b1;
  assign hw2reg.fault_status.phy_storage_err.d  = 1'b1;
  assign hw2reg.fault_status.spurious_ack.d     = 1'b1;
  assign hw2reg.fault_status.arb_err.d          = 1'b1;
  assign hw2reg.fault_status.host_gnt_err.d     = 1'b1;
  assign hw2reg.fault_status.op_err.de          = hw_err.invalid_op_err;
  assign hw2reg.fault_status.mp_err.de          = hw_err.mp_err;
  assign hw2reg.fault_status.rd_err.de          = hw_err.rd_err;
  assign hw2reg.fault_status.prog_err.de        = hw_err.prog_err;
  assign hw2reg.fault_status.prog_win_err.de    = hw_err.prog_win_err;
  assign hw2reg.fault_status.prog_type_err.de   = hw_err.prog_type_err;
  assign hw2reg.fault_status.seed_err.de        = seed_err;
  assign hw2reg.fault_status.phy_relbl_err.de   = flash_phy_rsp.storage_relbl_err;
  assign hw2reg.fault_status.phy_storage_err.de = flash_phy_rsp.storage_intg_err;
  assign hw2reg.fault_status.spurious_ack.de    = flash_phy_rsp.spurious_ack;
  assign hw2reg.fault_status.arb_err.de         = flash_phy_rsp.arb_err;
  assign hw2reg.fault_status.host_gnt_err.de    = flash_phy_rsp.host_gnt_err;

  // standard faults
  assign hw2reg.std_fault_status.reg_intg_err.d    = 1'b1;
  assign hw2reg.std_fault_status.prog_intg_err.d   = 1'b1;
  assign hw2reg.std_fault_status.lcmgr_err.d       = 1'b1;
  assign hw2reg.std_fault_status.lcmgr_intg_err.d  = 1'b1;
  assign hw2reg.std_fault_status.arb_fsm_err.d     = 1'b1;
  assign hw2reg.std_fault_status.storage_err.d     = 1'b1;
  assign hw2reg.std_fault_status.phy_fsm_err.d     = 1'b1;
  assign hw2reg.std_fault_status.ctrl_cnt_err.d    = 1'b1;
  assign hw2reg.std_fault_status.fifo_err.d        = 1'b1;
  assign hw2reg.std_fault_status.reg_intg_err.de   = intg_err | eflash_cmd_intg_err |
                                                     tl_gate_intg_err | tl_prog_gate_intg_err;
  assign hw2reg.std_fault_status.prog_intg_err.de  = flash_phy_rsp.prog_intg_err;
  assign hw2reg.std_fault_status.lcmgr_err.de      = lcmgr_err;
  assign hw2reg.std_fault_status.lcmgr_intg_err.de = lcmgr_intg_err;
  assign hw2reg.std_fault_status.arb_fsm_err.de    = arb_fsm_err;
  assign hw2reg.std_fault_status.storage_err.de    = storage_err;
  assign hw2reg.std_fault_status.phy_fsm_err.de    = flash_phy_rsp.fsm_err;
  assign hw2reg.std_fault_status.ctrl_cnt_err.de   = rd_cnt_err | prog_cnt_err;
  assign hw2reg.std_fault_status.fifo_err.de       = flash_phy_rsp.fifo_err | adapter_fifo_err;

  // Correctable ECC count / address
  for (genvar i = 0; i < NumBanks; i++) begin : gen_ecc_single_err_reg
    assign hw2reg.ecc_single_err_cnt[i].de = flash_phy_rsp.ecc_single_err[i];
    assign hw2reg.ecc_single_err_cnt[i].d = &reg2hw.ecc_single_err_cnt[i].q ?
                                            reg2hw.ecc_single_err_cnt[i].q :
                                            reg2hw.ecc_single_err_cnt[i].q + 1'b1;

    assign hw2reg.ecc_single_err_addr[i].de = flash_phy_rsp.ecc_single_err[i];
    assign hw2reg.ecc_single_err_addr[i].d = {flash_phy_rsp.ecc_addr[i], {BusByteWidth{1'b0}}};
  end

  logic sw_rd_fifo_wr_q;
  logic prog_fifo_rd_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sw_rd_fifo_wr_q <= '0;
      prog_fifo_rd_q <= '0;
    end else begin
      sw_rd_fifo_wr_q <= sw_rfifo_wen & sw_rfifo_wready;
      prog_fifo_rd_q <= prog_fifo_rvalid & prog_fifo_ren;
    end
  end

  // general interrupt events
  logic [LastIntrIdx-1:0] intr_event;

  prim_edge_detector #(
    .Width(1),
    .ResetValue(1),
    .EnSync(0)
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
    .ResetValue(0),
    .EnSync(0)
  ) u_prog_lvl_event (
    .clk_i,
    .rst_ni,
    .d_i(prog_fifo_rd_q & (reg2hw.fifo_lvl.prog.q == MaxFifoWidth'(prog_fifo_depth))),
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
    .ResetValue(0),
    .EnSync(0)
  ) u_rd_full_event (
    .clk_i,
    .rst_ni,
    .d_i(sw_rfifo_full),
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
    .ResetValue(0),
    .EnSync(0)
  ) u_rd_lvl_event (
    .clk_i,
    .rst_ni,
    .d_i(sw_rd_fifo_wr_q & (reg2hw.fifo_lvl.rd.q == sw_rfifo_depth)),
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
  logic [flash_ctrl_pkg::BusFullWidth-1:0] flash_host_rdata;
  logic [flash_ctrl_pkg::BusAddrW-1:0] flash_host_addr;

  lc_ctrl_pkg::lc_tx_t host_enable;

  // if flash disable is activated, error back from the adapter interface immediately
  assign host_enable = lc_ctrl_pkg::mubi4_to_lc_inv(flash_disable[HostDisableIdx]);

  tlul_pkg::tl_h2d_t gate_tl_h2d;
  tlul_pkg::tl_d2h_t gate_tl_d2h;

  // SEC_CM: MEM_TL_LC_GATE.FSM.SPARSE
  tlul_lc_gate u_tl_gate (
    .clk_i,
    .rst_ni,
    .tl_h2d_i(mem_tl_i),
    .tl_d2h_o(mem_tl_o),
    .tl_h2d_o(gate_tl_h2d),
    .tl_d2h_i(gate_tl_d2h),
    .flush_req_i('0),
    .flush_ack_o(),
    .resp_pending_o(),
    .lc_en_i(host_enable),
    .err_o(tl_gate_intg_err)
  );

  // SEC_CM: HOST.BUS.INTEGRITY
  tlul_adapter_sram #(
    .SramAw(BusAddrW),
    .SramDw(BusWidth),
    .Outstanding(2),
    .ByteAccess(0),
    .ErrOnWrite(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(0),
    .EnableDataIntgPt(1)
  ) u_tl_adapter_eflash (
    .clk_i,
    .rst_ni,
    .tl_i        (gate_tl_h2d),
    .tl_o        (gate_tl_d2h),
    .en_ifetch_i (flash_exec_en),
    .req_o       (flash_host_req),
    .req_type_o  (),
    .gnt_i       (flash_host_req_rdy),
    .we_o        (),
    .addr_o      (flash_host_addr),
    .wdata_o     (),
    .wmask_o     (),
    .intg_error_o(eflash_cmd_intg_err),
    .rdata_i     (flash_host_rdata),
    .rvalid_i    (flash_host_req_done),
    .rerror_i    ({flash_host_rderr,1'b0})
  );

  flash_phy #(
    .SecScrambleEn(SecScrambleEn)
  ) u_eflash (
    .clk_i,
    .rst_ni,
    .host_req_i        (flash_host_req),
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
    .fatal_prim_flash_alert_o(fatal_prim_flash_alert),
    .recov_prim_flash_alert_o(recov_prim_flash_alert),
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
  `ASSERT_KNOWN(TdoKnown_A,             cio_tdo_o        )
  `ASSERT(TdoEnIsOne_A,                 cio_tdo_en_o === 1'b1)

  // combined indication that an operation has started
  // This is used only for assertions
  logic unused_op_valid;
  assign unused_op_valid = prog_op_valid | rd_op_valid | erase_op_valid;

  // add more assertions
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(SeedCntAlertCheck_A, u_flash_hw_if.u_seed_cnt,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(AddrCntAlertCheck_A, u_flash_hw_if.u_addr_cnt,
                                         alert_tx_o[1])
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
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(TlLcGateFsm_A,
    u_tl_gate.u_state_regs, alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(TlProgLcGateFsm_A,
    u_prog_tl_gate.u_state_regs, alert_tx_o[1])

   for (genvar i=0; i<NumBanks; i++) begin : gen_phy_assertions
     `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(PhyFsmCheck_A,
       u_eflash.gen_flash_cores[i].u_core.u_state_regs, alert_tx_o[1])

     `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(PhyProgFsmCheck_A,
       u_eflash.gen_flash_cores[i].u_core.gen_prog_data.u_prog.u_state_regs, alert_tx_o[1])
   end

  `ifdef INC_ASSERT
   `define PHY u_eflash.gen_flash_cores[i]
   `define PHY_CORE `PHY.u_core
   for (genvar i=0; i<NumBanks; i++) begin : gen_phy_cnt_errs
     `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PhyRspFifoWPtr_A,
       `PHY.u_host_rsp_fifo.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_wptr, alert_tx_o[1])

     `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PhyRspFifoRPtr_A,
       `PHY.u_host_rsp_fifo.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_rptr, alert_tx_o[1])

     `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PhyRdRspFifoWPtr_A,
       `PHY_CORE.u_rd.u_rsp_order_fifo.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_wptr,
       alert_tx_o[1])

     `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PhyRdRspFifoRPtr_A,
       `PHY_CORE.u_rd.u_rsp_order_fifo.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_rptr,
       alert_tx_o[1])

     `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PhyRdDataFifoWPtr_A,
       `PHY_CORE.u_rd.u_rd_storage.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_wptr,
       alert_tx_o[1])

     `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PhyRdDataFifoRPtr_A,
       `PHY_CORE.u_rd.u_rd_storage.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_rptr,
       alert_tx_o[1])

     // Outstanding count error is merged into host_gnt_err instead of being an
     // individual count error.
     `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(PhyHostCnt_A,
       `PHY_CORE.u_host_outstanding_cnt, alert_tx_o[2])
   end
   `endif

  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(RdFifoWptrCheck_A,
      u_to_rd_fifo.u_rspfifo.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_wptr,
      alert_tx_o[1])

  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(RdFifoRptrCheck_A,
      u_to_rd_fifo.u_rspfifo.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.u_rptr,
      alert_tx_o[1])

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg_core, alert_tx_o[1])

  // Assertions for countermeasures inside prim_flash
  `ifndef PRIM_DEFAULT_IMPL
    `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
  `endif
  if (`PRIM_DEFAULT_IMPL == prim_pkg::ImplGeneric) begin : gen_reg_we_assert_generic
    `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(PrimRegWeOnehotCheck_A,
        u_eflash.u_flash.gen_generic.u_impl_generic.u_reg_top, alert_tx_o[3])
  end

endmodule
