// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Ibex RISC-V core
 *
 * 32 bit RISC-V core supporting the RV32I + optionally EMC instruction sets.
 * Instruction and data bus are 32 bit wide TileLink-UL (TL-UL).
 */
module rv_core_ibex
  import rv_core_ibex_pkg::*;
  import rv_core_ibex_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn     = {NumAlerts{1'b1}},
  parameter bit                   PMPEnable        = 1'b1,
  parameter int unsigned          PMPGranularity   = 0,
  parameter int unsigned          PMPNumRegions    = 16,
  parameter int unsigned          MHPMCounterNum   = 10,
  parameter int unsigned          MHPMCounterWidth = 32,
  parameter bit                   RV32E            = 0,
  parameter ibex_pkg::rv32m_e     RV32M            = ibex_pkg::RV32MSingleCycle,
  parameter ibex_pkg::rv32b_e     RV32B            = ibex_pkg::RV32BOTEarlGrey,
  parameter ibex_pkg::regfile_e   RegFile          = ibex_pkg::RegFileFF,
  parameter bit                   BranchTargetALU  = 1'b1,
  parameter bit                   WritebackStage   = 1'b1,
  parameter bit                   ICache           = 1'b1,
  parameter bit                   ICacheECC        = 1'b1,
  parameter bit                   ICacheScramble   = 1'b1,
  parameter bit                   BranchPredictor  = 1'b0,
  parameter bit                   DbgTriggerEn     = 1'b1,
  parameter int unsigned          DbgHwBreakNum    = 4,
  parameter bit                   SecureIbex       = 1'b1,
  parameter ibex_pkg::lfsr_seed_t RndCnstLfsrSeed  = ibex_pkg::RndCnstLfsrSeedDefault,
  parameter ibex_pkg::lfsr_perm_t RndCnstLfsrPerm  = ibex_pkg::RndCnstLfsrPermDefault,
  parameter int unsigned          DmHaltAddr       = 32'h1A110800,
  parameter int unsigned          DmExceptionAddr  = 32'h1A110808,
  parameter bit                   PipeLine         = 1'b0,
  parameter logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] RndCnstIbexKeyDefault =
      ibex_pkg::RndCnstIbexKeyDefault,
  parameter logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] RndCnstIbexNonceDefault =
      ibex_pkg::RndCnstIbexNonceDefault
) (
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,
  // Clock domain for edn
  input  logic        clk_edn_i,
  input  logic        rst_edn_ni,
  // Clock domain for escalation receiver
  input  logic        clk_esc_i,
  input  logic        rst_esc_ni,
  // Reset feedback to rstmgr
  output logic        rst_cpu_n_o,

  input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

  input  logic [31:0] hart_id_i,
  input  logic [31:0] boot_addr_i,

  // Instruction memory interface
  output tlul_pkg::tl_h2d_t     corei_tl_h_o,
  input  tlul_pkg::tl_d2h_t     corei_tl_h_i,

  // Data memory interface
  output tlul_pkg::tl_h2d_t     cored_tl_h_o,
  input  tlul_pkg::tl_d2h_t     cored_tl_h_i,

  // Interrupt inputs
  input  logic        irq_software_i,
  input  logic        irq_timer_i,
  input  logic        irq_external_i,

  // Escalation input for NMI
  input  prim_esc_pkg::esc_tx_t esc_tx_i,
  output prim_esc_pkg::esc_rx_t esc_rx_o,

  // watchdog NMI input
  input logic nmi_wdog_i,

  // Debug Interface
  input  logic        debug_req_i,

  // Crash dump information
  output cpu_crash_dump_t crash_dump_o,

  // CPU Control Signals
  input lc_ctrl_pkg::lc_tx_t lc_cpu_en_i,
  input lc_ctrl_pkg::lc_tx_t pwrmgr_cpu_en_i,
  output pwrmgr_pkg::pwr_cpu_t pwrmgr_o,

  // dft bypass
  input scan_rst_ni,
  input prim_mubi_pkg::mubi4_t scanmode_i,

  // peripheral interface access
  input  tlul_pkg::tl_h2d_t cfg_tl_d_i,
  output tlul_pkg::tl_d2h_t cfg_tl_d_o,

  // connection to edn
  output edn_pkg::edn_req_t edn_o,
  input edn_pkg::edn_rsp_t edn_i,

  // connection to otp scramble interface
  input clk_otp_i,
  input rst_otp_ni,
  output otp_ctrl_pkg::sram_otp_key_req_t icache_otp_key_o,
  input  otp_ctrl_pkg::sram_otp_key_rsp_t icache_otp_key_i,

  // fpga build info
  input [31:0] fpga_info_i,

  // interrupts and alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o

);

  import top_pkg::*;
  import tlul_pkg::*;

  // Register module
  rv_core_ibex_cfg_reg2hw_t reg2hw;
  rv_core_ibex_cfg_hw2reg_t hw2reg;

  // if pipeline=1, do not allow pass through and always break the path
  // if pipeline is 0, passthrough the fifo completely
  localparam bit FifoPass = PipeLine ? 1'b0 : 1'b1;
  localparam int unsigned FifoDepth = PipeLine ? 2 : 0;
  // ICache creates more outstanding transactions
  localparam int NumOutstandingReqs = ICache ? 8 : 2;

  // Instruction interface (internal)
  logic        instr_req;
  logic        instr_gnt;
  logic        instr_rvalid;
  logic [31:0] instr_addr;
  logic [31:0] instr_rdata;
  logic [6:0]  instr_rdata_intg;
  logic        instr_err;

  // Data interface (internal)
  logic        data_req;
  logic        data_gnt;
  logic        data_rvalid;
  logic        data_we;
  logic [3:0]  data_be;
  logic [31:0] data_addr;
  logic [31:0] data_wdata;
  logic [6:0]  data_wdata_intg;
  logic [31:0] data_rdata;
  logic [6:0]  data_rdata_intg;
  logic        data_err;

  // Pipeline interfaces
  tl_h2d_t tl_i_ibex2fifo;
  tl_d2h_t tl_i_fifo2ibex;
  tl_h2d_t tl_d_ibex2fifo;
  tl_d2h_t tl_d_fifo2ibex;

`ifdef RVFI
  logic        rvfi_valid;
  logic [63:0] rvfi_order;
  logic [31:0] rvfi_insn;
  logic        rvfi_trap;
  logic        rvfi_halt;
  logic        rvfi_intr;
  logic [ 1:0] rvfi_mode;
  logic [ 1:0] rvfi_ixl;
  logic [ 4:0] rvfi_rs1_addr;
  logic [ 4:0] rvfi_rs2_addr;
  logic [ 4:0] rvfi_rs3_addr;
  logic [31:0] rvfi_rs1_rdata;
  logic [31:0] rvfi_rs2_rdata;
  logic [31:0] rvfi_rs3_rdata;
  logic [ 4:0] rvfi_rd_addr;
  logic [31:0] rvfi_rd_wdata;
  logic [31:0] rvfi_pc_rdata;
  logic [31:0] rvfi_pc_wdata;
  logic [31:0] rvfi_mem_addr;
  logic [ 3:0] rvfi_mem_rmask;
  logic [ 3:0] rvfi_mem_wmask;
  logic [31:0] rvfi_mem_rdata;
  logic [31:0] rvfi_mem_wdata;
`endif

  // core sleeping
  logic core_sleep;

  // The following intermediate signals are created to aid in simulations.
  //
  // If a parent port is connected directly to a port of sub-modules, the implicit wire connection
  // can have only one procedural driver (assign, force etc). What that means is, it prevents us
  // from forcing the sub-module port without impacting the same port on other sub-modules. The
  // reason for this is, regardless of which hierarchy the port signal is forced, it is a singular
  // wire-connected entity - the effect of the force ends up getting reflected on the same port of
  // sub-modules, as well as the parent port. To achieve the behavior of a force on a sub-module
  // port not impacting (i.e. back-propagating to) the same port on parent / peer sub-modules, we
  // need to add an extra `logic` type variables between the port-port connections.
  logic ibex_top_clk_i;
  logic addr_trans_rst_ni;
  assign ibex_top_clk_i = clk_i;
  assign addr_trans_rst_ni = rst_ni;

  // errors and core alert events
  logic ibus_intg_err, dbus_intg_err;
  logic alert_minor, alert_major_internal, alert_major_bus;
  logic double_fault;
  logic fatal_intg_err, fatal_core_err, recov_core_err;

  // alert events to peripheral module
  logic fatal_intg_event;
  logic fatal_core_event;
  logic recov_core_event;
  // SEC_CM: BUS.INTEGRITY
  assign fatal_intg_event = ibus_intg_err | dbus_intg_err | alert_major_bus;
  assign fatal_core_event = alert_major_internal | double_fault;
  assign recov_core_event = alert_minor;

  // configurations for address translation
  region_cfg_t [NumRegions-1:0] ibus_region_cfg;
  region_cfg_t [NumRegions-1:0] dbus_region_cfg;

  // Reset feedback to clkmgr
  assign rst_cpu_n_o = rst_ni;

  // Escalation receiver that converts differential
  // protocol into single ended signal.
  logic esc_irq_nm;
  prim_esc_receiver #(
    .N_ESC_SEV   (alert_handler_reg_pkg::N_ESC_SEV),
    .PING_CNT_DW (alert_handler_reg_pkg::PING_CNT_DW)
  ) u_prim_esc_receiver (
    .clk_i     ( clk_esc_i  ),
    .rst_ni    ( rst_esc_ni ),
    .esc_req_o ( esc_irq_nm ),
    .esc_rx_o,
    .esc_tx_i
  );

  // Synchronize to fast Ibex clock domain.
  logic alert_irq_nm;
  prim_flop_2sync #(
    .Width(1)
  ) u_alert_nmi_sync (
    .clk_i,
    .rst_ni,
    .d_i(esc_irq_nm),
    .q_o(alert_irq_nm)
  );

  logic wdog_irq_nm;
  prim_flop_2sync #(
    .Width(1)
  ) u_wdog_nmi_sync (
    .clk_i,
    .rst_ni,
    .d_i(nmi_wdog_i),
    .q_o(wdog_irq_nm)
  );

  assign hw2reg.nmi_state.alert.d  = 1'b1;
  assign hw2reg.nmi_state.alert.de = alert_irq_nm;
  assign hw2reg.nmi_state.wdog.d   = 1'b1;
  assign hw2reg.nmi_state.wdog.de  = wdog_irq_nm;

  logic irq_nm;
  assign irq_nm = |(reg2hw.nmi_state & reg2hw.nmi_enable);

  lc_ctrl_pkg::lc_tx_t [0:0] lc_cpu_en;
  prim_lc_sync u_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_cpu_en_i),
    .lc_en_o(lc_cpu_en)
  );

  lc_ctrl_pkg::lc_tx_t [0:0] pwrmgr_cpu_en;
  prim_lc_sync u_pwrmgr_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(pwrmgr_cpu_en_i),
    .lc_en_o(pwrmgr_cpu_en)
  );

  // TODO: This is a hoaky fix, we really should converge everthing
  // through rv_plic.
  // timer interrupts do not come from
  // rv_plic and may not be synchronous to the ibex core
  logic irq_timer_sync;
  prim_flop_2sync #(
    .Width(1)
  ) u_intr_timer_sync (
    .clk_i,
    .rst_ni,
    .d_i(irq_timer_i),
    .q_o(irq_timer_sync)
  );


  logic irq_software;
  logic irq_timer;
  logic irq_external;

  prim_sec_anchor_buf #(
    .Width(3)
  ) u_prim_buf_irq (
    .in_i({irq_software_i,
           irq_timer_sync,
           irq_external_i}),
    .out_o({irq_software,
            irq_timer,
            irq_external})
  );


  logic key_req, key_ack;
  logic [ibex_pkg::SCRAMBLE_KEY_W-1:0] key;
  logic [ibex_pkg::SCRAMBLE_NONCE_W-1:0] nonce;
  logic unused_seed_valid;
  localparam int PayLoadW = ibex_pkg::SCRAMBLE_KEY_W + ibex_pkg::SCRAMBLE_NONCE_W + 1;
  prim_sync_reqack_data #(
    .Width(PayLoadW),
    .DataSrc2Dst(1'b0)
  ) u_prim_sync_reqack_data (
    .clk_src_i  ( clk_i                         ),
    .rst_src_ni ( rst_ni                        ),
    .clk_dst_i  ( clk_otp_i                     ),
    .rst_dst_ni ( rst_otp_ni                    ),
    .req_chk_i  ( 1'b1                          ),
    .src_req_i  ( key_req                       ),
    .src_ack_o  ( key_ack                       ),
    .dst_req_o  ( icache_otp_key_o.req          ),
    .dst_ack_i  ( icache_otp_key_i.ack          ),
    .data_i     ( {icache_otp_key_i.key,
                   icache_otp_key_i.nonce[ibex_pkg::SCRAMBLE_NONCE_W-1:0],
                   icache_otp_key_i.seed_valid} ),
    .data_o     ( {key,
                   nonce,
                   unused_seed_valid}           )
  );

  logic unused_nonce;
  assign unused_nonce = |icache_otp_key_i.nonce;

  // Local fetch enable control.
  // Whenever a fatal core error is seen disable local fetch enable.
  lc_ctrl_pkg::lc_tx_t local_fetch_enable_d, local_fetch_enable_q;

  assign local_fetch_enable_d = fatal_core_err ? lc_ctrl_pkg::Off : local_fetch_enable_q;

  prim_lc_sender #(
    .AsyncOn(1), // this instantiates a register
    .ResetValueIsOn(1)
  ) u_prim_lc_sender (
    .clk_i,
    .rst_ni,
    .lc_en_i(local_fetch_enable_d),
    .lc_en_o(local_fetch_enable_q)
  );

  // Multibit AND computation for fetch enable. Fetch is only enabled when local fetch enable,
  // lifecycle CPU enable and power manager CPU enable are all enabled.
  lc_ctrl_pkg::lc_tx_t fetch_enable;
  assign fetch_enable = lc_ctrl_pkg::lc_tx_and_hi(local_fetch_enable_q,
                                                  lc_ctrl_pkg::lc_tx_and_hi(lc_cpu_en[0],
                                                                            pwrmgr_cpu_en[0]));

  ibex_pkg::crash_dump_t crash_dump;
  ibex_top #(
    .PMPEnable                ( PMPEnable                ),
    .PMPGranularity           ( PMPGranularity           ),
    .PMPNumRegions            ( PMPNumRegions            ),
    .MHPMCounterNum           ( MHPMCounterNum           ),
    .MHPMCounterWidth         ( MHPMCounterWidth         ),
    .RV32E                    ( RV32E                    ),
    .RV32M                    ( RV32M                    ),
    .RV32B                    ( RV32B                    ),
    .RegFile                  ( RegFile                  ),
    .BranchTargetALU          ( BranchTargetALU          ),
    .WritebackStage           ( WritebackStage           ),
    .ICache                   ( ICache                   ),
    // Our automatic SEC_CM label check doesn't look at vendored code so the SEC_CM labels need
    // to be mentioned here. The real locations can be found by grepping the vendored code.
    // TODO(#10071): this should be fixed.
    // SEC_CM: ICACHE.MEM.INTEGRITY
    .ICacheECC                ( ICacheECC                ),
    // SEC_CM: ICACHE.MEM.SCRAMBLE, SCRAMBLE.KEY.SIDELOAD
    .ICacheScramble           ( ICacheScramble           ),
    .BranchPredictor          ( BranchPredictor          ),
    .DbgTriggerEn             ( DbgTriggerEn             ),
    .DbgHwBreakNum            ( DbgHwBreakNum            ),
    // SEC_CM: LOGIC.SHADOW
    // SEC_CM: PC.CTRL_FLOW.CONSISTENCY, CTRL_FLOW.UNPREDICTABLE, CORE.DATA_REG_SW.SCA
    // SEC_CM: EXCEPTION.CTRL_FLOW.GLOBAL_ESC, EXCEPTION.CTRL_FLOW.LOCAL_ESC
    // SEC_CM: DATA_REG_SW.INTEGRITY, DATA_REG_SW.GLITCH_DETECT
    .SecureIbex               ( SecureIbex               ),
    .RndCnstLfsrSeed          ( RndCnstLfsrSeed          ),
    .RndCnstLfsrPerm          ( RndCnstLfsrPerm          ),
    .RndCnstIbexKey           ( RndCnstIbexKeyDefault    ),
    .RndCnstIbexNonce         ( RndCnstIbexNonceDefault  ),
    .DmHaltAddr               ( DmHaltAddr               ),
    .DmExceptionAddr          ( DmExceptionAddr          )
  ) u_core (
    .clk_i              (ibex_top_clk_i),
    .rst_ni,


    .test_en_i          (prim_mubi_pkg::mubi4_test_true_strict(scanmode_i)),
    .scan_rst_ni,

    .ram_cfg_i,

    .hart_id_i,
    .boot_addr_i,

    .instr_req_o        ( instr_req        ),
    .instr_gnt_i        ( instr_gnt        ),
    .instr_rvalid_i     ( instr_rvalid     ),
    .instr_addr_o       ( instr_addr       ),
    .instr_rdata_i      ( instr_rdata      ),
    .instr_rdata_intg_i ( instr_rdata_intg ),
    .instr_err_i        ( instr_err        ),

    .data_req_o         ( data_req         ),
    .data_gnt_i         ( data_gnt         ),
    .data_rvalid_i      ( data_rvalid      ),
    .data_we_o          ( data_we          ),
    .data_be_o          ( data_be          ),
    .data_addr_o        ( data_addr        ),
    .data_wdata_o       ( data_wdata       ),
    .data_wdata_intg_o  ( data_wdata_intg  ),
    .data_rdata_i       ( data_rdata       ),
    .data_rdata_intg_i  ( data_rdata_intg  ),
    .data_err_i         ( data_err         ),

    .irq_software_i     ( irq_software     ),
    .irq_timer_i        ( irq_timer        ),
    .irq_external_i     ( irq_external     ),
    .irq_fast_i         ( '0               ),
    .irq_nm_i           ( irq_nm           ),

    .debug_req_i,
    .crash_dump_o       ( crash_dump       ),

    // icache scramble interface
    .scramble_key_valid_i (key_ack),
    .scramble_key_i       (key),
    .scramble_nonce_i     (nonce),
    .scramble_req_o       (key_req),

    // double fault
    .double_fault_seen_o  (double_fault),

`ifdef RVFI
    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs2_rdata,
    .rvfi_rs3_rdata,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata,
`endif
    // SEC_CM: FETCH.CTRL.LC_GATED
    .fetch_enable_i         (fetch_enable),
    .alert_minor_o          (alert_minor),
    .alert_major_internal_o (alert_major_internal),
    .alert_major_bus_o      (alert_major_bus),
    .core_sleep_o           (core_sleep)
  );

  logic core_sleep_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      core_sleep_q <= '0;
    end else begin
      core_sleep_q <= core_sleep;
    end
  end

  prim_buf #(
    .Width(1)
  ) u_core_sleeping_buf (
    .in_i(core_sleep_q),
    .out_o(pwrmgr_o.core_sleeping)
  );



  logic prev_valid;
  logic [31:0] prev_exception_pc;
  logic [31:0] prev_exception_addr;

  assign crash_dump_o.current = crash_dump;
  assign crash_dump_o.prev_valid = prev_valid;
  assign crash_dump_o.prev_exception_pc = prev_exception_pc;
  assign crash_dump_o.prev_exception_addr = prev_exception_addr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prev_valid <= '0;
      prev_exception_pc <= '0;
      prev_exception_addr <= '0;
    end else if (double_fault) begin
      prev_valid <= 1'b1;
      prev_exception_pc <= crash_dump.exception_pc;
      prev_exception_addr <= crash_dump.exception_addr;
    end
  end


  //
  // Convert ibex data/instruction bus to TL-UL
  //
  logic [31:0] instr_addr_trans;
  rv_core_addr_trans #(
    .AddrWidth(32),
    .NumRegions(NumRegions)
  ) u_ibus_trans (
    .clk_i,
    .rst_ni(addr_trans_rst_ni),
    .region_cfg_i(ibus_region_cfg),
    .addr_i(instr_addr),
    .addr_o(instr_addr_trans)
  );

  logic [6:0]  instr_wdata_intg;
  logic [top_pkg::TL_DW-1:0] unused_data;
  // tl_adapter_host_i_ibex only reads instruction. a_data is always 0
  assign {instr_wdata_intg, unused_data} = prim_secded_pkg::prim_secded_inv_39_32_enc('0);
  // SEC_CM: BUS.INTEGRITY
  tlul_adapter_host #(
    .MAX_REQS(NumOutstandingReqs),
    // if secure ibex is not set, data integrity is not generated
    // from ibex, therefore generate it in the gasket instead.
    .EnableDataIntgGen(~SecureIbex)
  ) tl_adapter_host_i_ibex (
    .clk_i,
    .rst_ni,
    .req_i        (instr_req),
    .instr_type_i (prim_mubi_pkg::MuBi4True),
    .gnt_o        (instr_gnt),
    .addr_i       (instr_addr_trans),
    .we_i         (1'b0),
    .wdata_i      (32'b0),
    .wdata_intg_i (instr_wdata_intg),
    .be_i         (4'hF),
    .valid_o      (instr_rvalid),
    .rdata_o      (instr_rdata),
    .rdata_intg_o (instr_rdata_intg),
    .err_o        (instr_err),
    .intg_err_o   (ibus_intg_err),
    .tl_o         (tl_i_ibex2fifo),
    .tl_i         (tl_i_fifo2ibex)
  );

  tlul_fifo_sync #(
    .ReqPass(FifoPass),
    .RspPass(FifoPass),
    .ReqDepth(FifoDepth),
    .RspDepth(FifoDepth)
  ) fifo_i (
    .clk_i,
    .rst_ni,
    .tl_h_i      (tl_i_ibex2fifo),
    .tl_h_o      (tl_i_fifo2ibex),
    .tl_d_o      (corei_tl_h_o),
    .tl_d_i      (corei_tl_h_i),
    .spare_req_i (1'b0),
    .spare_req_o (),
    .spare_rsp_i (1'b0),
    .spare_rsp_o ());

  logic [31:0] data_addr_trans;
  rv_core_addr_trans #(
    .AddrWidth(32),
    .NumRegions(NumRegions)
  ) u_dbus_trans (
    .clk_i,
    .rst_ni(addr_trans_rst_ni),
    .region_cfg_i(dbus_region_cfg),
    .addr_i(data_addr),
    .addr_o(data_addr_trans)
  );

  // SEC_CM: BUS.INTEGRITY
  tlul_adapter_host #(
    .MAX_REQS(2),
    .EnableDataIntgGen(~SecureIbex)
  ) tl_adapter_host_d_ibex (
    .clk_i,
    .rst_ni,
    .req_i        (data_req),
    .instr_type_i (prim_mubi_pkg::MuBi4False),
    .gnt_o        (data_gnt),
    .addr_i       (data_addr_trans),
    .we_i         (data_we),
    .wdata_i      (data_wdata),
    .wdata_intg_i (data_wdata_intg),
    .be_i         (data_be),
    .valid_o      (data_rvalid),
    .rdata_o      (data_rdata),
    .rdata_intg_o (data_rdata_intg),
    .err_o        (data_err),
    .intg_err_o   (dbus_intg_err),
    .tl_o         (tl_d_ibex2fifo),
    .tl_i         (tl_d_fifo2ibex)
  );

  tlul_fifo_sync #(
    .ReqPass(FifoPass),
    .RspPass(FifoPass),
    .ReqDepth(FifoDepth),
    .RspDepth(FifoDepth)
  ) fifo_d (
    .clk_i,
    .rst_ni,
    .tl_h_i      (tl_d_ibex2fifo),
    .tl_h_o      (tl_d_fifo2ibex),
    .tl_d_o      (cored_tl_h_o),
    .tl_d_i      (cored_tl_h_i),
    .spare_req_i (1'b0),
    .spare_req_o (),
    .spare_rsp_i (1'b0),
    .spare_rsp_o ());

`ifdef RVFI
  ibex_tracer ibex_tracer_i (
    .clk_i,
    .rst_ni,

    .hart_id_i,

    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs2_rdata,
    .rvfi_rs3_rdata,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata
  );
`endif

  //////////////////////////////////
  // Peripheral functions
  //////////////////////////////////

  logic intg_err;
  tlul_pkg::tl_h2d_t tl_win_h2d;
  tlul_pkg::tl_d2h_t tl_win_d2h;
  rv_core_ibex_cfg_reg_top u_reg_cfg (
    .clk_i,
    .rst_ni,
    .tl_i(cfg_tl_d_i),
    .tl_o(cfg_tl_d_o),
    .reg2hw,
    .hw2reg,
    .intg_err_o (intg_err),
    .tl_win_o(tl_win_h2d),
    .tl_win_i(tl_win_d2h),
    .devmode_i  (1'b1) // connect to real devmode signal in the future
  );

  ///////////////////////
  // Region assignments
  ///////////////////////

  for(genvar i = 0; i < NumRegions; i++) begin : gen_ibus_region_cfgs
    assign ibus_region_cfg[i].en = reg2hw.ibus_addr_en[i];
    assign ibus_region_cfg[i].matching_region = reg2hw.ibus_addr_matching[i];
    assign ibus_region_cfg[i].remap_addr = reg2hw.ibus_remap_addr[i];
  end

  for(genvar i = 0; i < NumRegions; i++) begin : gen_dbus_region_cfgs
    assign dbus_region_cfg[i].en = reg2hw.dbus_addr_en[i];
    assign dbus_region_cfg[i].matching_region = reg2hw.dbus_addr_matching[i];
    assign dbus_region_cfg[i].remap_addr = reg2hw.dbus_remap_addr[i];
  end

  ///////////////////////
  // Error assignment
  ///////////////////////

  assign fatal_intg_err = fatal_intg_event;
  assign fatal_core_err = fatal_core_event;
  assign recov_core_err = recov_core_event;

  assign hw2reg.err_status.reg_intg_err.d = 1'b1;
  assign hw2reg.err_status.reg_intg_err.de = intg_err;
  assign hw2reg.err_status.fatal_intg_err.d = 1'b1;
  assign hw2reg.err_status.fatal_intg_err.de = fatal_intg_err;
  assign hw2reg.err_status.fatal_core_err.d = 1'b1;
  assign hw2reg.err_status.fatal_core_err.de = fatal_core_err;
  assign hw2reg.err_status.recov_core_err.d = 1'b1;
  assign hw2reg.err_status.recov_core_err.de = recov_core_err;

  ///////////////////////
  // Alert generation
  ///////////////////////

  logic [NumAlerts-1:0] alert_test;
  assign alert_test[0] = reg2hw.alert_test.fatal_sw_err.q &
                         reg2hw.alert_test.fatal_sw_err.qe;
  assign alert_test[1] = reg2hw.alert_test.recov_sw_err.q &
                         reg2hw.alert_test.recov_sw_err.qe;
  assign alert_test[2] = reg2hw.alert_test.fatal_hw_err.q &
                         reg2hw.alert_test.fatal_hw_err.qe;
  assign alert_test[3] = reg2hw.alert_test.recov_hw_err.q &
                         reg2hw.alert_test.recov_hw_err.qe;

  localparam bit [NumAlerts-1:0] AlertFatal = '{1'b0, 1'b1, 1'b0, 1'b1};

  logic [NumAlerts-1:0] alert_events;
  logic [NumAlerts-1:0] alert_acks;

  import prim_mubi_pkg::mubi4_test_true_loose;
  import prim_mubi_pkg::mubi4_t;
  assign alert_events[0] = mubi4_test_true_loose(mubi4_t'(reg2hw.sw_fatal_err.q));
  assign alert_events[1] = mubi4_test_true_loose(mubi4_t'(reg2hw.sw_recov_err.q));
  assign alert_events[2] = intg_err | fatal_intg_err | fatal_core_err;
  assign alert_events[3] = recov_core_err;

  logic unused_alert_acks;
  assign unused_alert_acks = |alert_acks;

  // recoverable alerts are sent once and silenced until activated again.
  assign hw2reg.sw_recov_err.de = alert_acks[1];
  assign hw2reg.sw_recov_err.d = prim_mubi_pkg::MuBi4False;

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_senders
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[0]),
      .IsFatal(AlertFatal[i])
    ) u_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i(alert_test[i]),
      .alert_req_i(alert_events[i]),
      .alert_ack_o(alert_acks[i]),
      .alert_state_o(),
      .alert_rx_i(alert_rx_i[i]),
      .alert_tx_o(alert_tx_o[i])
    );
  end

  //////////////
  // RND Data //
  //////////////

  logic [31:0] rnd_data_q, rnd_data_d;
  logic rnd_valid_q, rnd_valid_d;
  logic rnd_fips_q, rnd_fips_d;
  logic edn_req;
  logic [31:0] edn_data;
  logic edn_ack;
  logic edn_fips;

  always_comb begin
    rnd_valid_d = rnd_valid_q;
    rnd_data_d  = rnd_data_q;
    rnd_fips_d  = rnd_fips_q;

    if (reg2hw.rnd_data.re) begin
      rnd_valid_d = '0;
      rnd_data_d  = '0;
      rnd_fips_d  = '0;
    end else if (edn_req && edn_ack) begin
      rnd_valid_d = 1'b1;
      rnd_data_d  = edn_data;
      rnd_fips_d  = edn_fips;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rnd_valid_q <= '0;
      rnd_data_q  <= '0;
      rnd_fips_q  <= '0;
    end else begin
      rnd_valid_q <= rnd_valid_d;
      rnd_data_q  <= rnd_data_d;
      rnd_fips_q  <= rnd_fips_d;
    end
  end

  assign edn_req = ~rnd_valid_q;

  prim_edn_req #(
    .OutWidth(32)
  ) u_edn_if (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b1),
    .req_i(edn_req),
    .ack_o(edn_ack),
    .data_o(edn_data),
    .fips_o(edn_fips),
    .err_o(),
    .clk_edn_i,
    .rst_edn_ni,
    .edn_o,
    .edn_i
  );

  assign hw2reg.rnd_data.d                  = rnd_data_q;
  assign hw2reg.rnd_status.rnd_data_valid.d = rnd_valid_q;
  assign hw2reg.rnd_status.rnd_data_fips.d  = rnd_fips_q;

  logic unused_reg2hw;
  assign unused_reg2hw = |reg2hw.rnd_data.q;


  // fpga build info hook-up
  assign hw2reg.fpga_info.d = fpga_info_i;

  /////////////////////////////////////
  // The carved out space is for DV emulation purposes only
  /////////////////////////////////////

  import tlul_pkg::tl_h2d_t;
  import tlul_pkg::tl_d2h_t;
  localparam int TlH2DWidth = $bits(tl_h2d_t);
  localparam int TlD2HWidth = $bits(tl_d2h_t);

  logic [TlH2DWidth-1:0] tl_win_h2d_int;
  logic [TlD2HWidth-1:0] tl_win_d2h_int;
  tl_d2h_t tl_win_d2h_err_rsp;

  prim_buf #(
    .Width(TlH2DWidth)
  ) u_tlul_req_buf (
    .in_i(tl_win_h2d),
    .out_o(tl_win_h2d_int)
  );

  prim_buf #(
    .Width(TlD2HWidth)
  ) u_tlul_rsp_buf (
    .in_i(tl_win_d2h_err_rsp),
    .out_o(tl_win_d2h_int)
  );

  // Interception point for connecting simulation SRAM by disconnecting the tl_d output. The
  // disconnection is done only if `SYNTHESIS is NOT defined AND `RV_CORE_IBEX_SIM_SRAM is
  // defined.
  // This define is used only for verilator as verilator does not support forces.
`ifdef RV_CORE_IBEX_SIM_SRAM
`ifdef SYNTHESIS
  // Induce a compilation error by instantiating a non-existent module.
  illegal_preprocessor_branch_taken u_illegal_preprocessor_branch_taken();
`endif
`else
  assign tl_win_d2h = tl_d2h_t'(tl_win_d2h_int);
`endif

  tlul_err_resp u_sim_win_rsp (
    .clk_i,
    .rst_ni,
    .tl_h_i(tl_h2d_t'(tl_win_h2d_int)),
    .tl_h_o(tl_win_d2h_err_rsp)
  );

  // Assertions for CPU enable
  `ASSERT(FpvSecCmIbexFetchEnable0_A,
      fatal_core_err
      |=>
      lc_ctrl_pkg::lc_tx_test_false_loose(fetch_enable))
  `ASSERT(FpvSecCmIbexFetchEnable1_A,
      lc_ctrl_pkg::lc_tx_test_false_loose(lc_cpu_en_i)
      |->
      ##2 lc_ctrl_pkg::lc_tx_test_false_loose(fetch_enable))
  `ASSERT(FpvSecCmIbexFetchEnable2_A,
      lc_ctrl_pkg::lc_tx_test_false_loose(pwrmgr_cpu_en_i)
      |->
      ##2 lc_ctrl_pkg::lc_tx_test_false_loose(fetch_enable))
  `ASSERT(FpvSecCmIbexFetchEnable3_A,
      lc_ctrl_pkg::lc_tx_test_true_strict(lc_cpu_en_i) &&
      lc_ctrl_pkg::lc_tx_test_true_strict(pwrmgr_cpu_en_i) ##1
      lc_ctrl_pkg::lc_tx_test_true_strict(local_fetch_enable_q) &&
      !fatal_core_err
      |=>
      lc_ctrl_pkg::lc_tx_test_true_strict(fetch_enable))
  `ASSERT(FpvSecCmIbexFetchEnable3Rev_A,
      ##2 lc_ctrl_pkg::lc_tx_test_true_strict(fetch_enable)
      |->
      $past(lc_ctrl_pkg::lc_tx_test_true_strict(lc_cpu_en_i), 2) &&
      $past(lc_ctrl_pkg::lc_tx_test_true_strict(pwrmgr_cpu_en_i), 2) &&
      $past(!fatal_core_err))

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg_cfg, alert_tx_o[2])
  `ASSERT_PRIM_ONEHOT_ERROR_TRIGGER_ALERT(RvCoreRegWeOnehotCheck_A,
      u_core.gen_regfile_ff.register_file_i.gen_wren_check.u_prim_onehot_check, alert_tx_o[2])

`ifdef INC_ASSERT
  if (ICache && ICacheScramble) begin : gen_icache_scramble_asserts

    // Sample icache scramble key for use in assertions below.
    // pragma coverage off
    //VCS coverage off
    logic [otp_ctrl_pkg::FlashKeyWidth-1:0] icache_otp_key_q;
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
        icache_otp_key_q <= '0;
      end else if (icache_otp_key_i.ack) begin
        icache_otp_key_q <= icache_otp_key_i.key;
      end
    end
    //VCS coverage on
    // pragma coverage on

    // Ensure that when a scramble key is received, it is correctly forwarded to the core.  The core
    // will then internally ensure that the key is correctly applied to the icache scrambled
    // memory primitives.
    `ASSERT(IbexIcacheScrambleKeyForwardedToCore_A,
            icache_otp_key_i.ack
            |-> ##[0:10] // upper bound is not exact, but it should not take more than 10 cycles
            u_core.scramble_key_valid_i && (u_core.scramble_key_i == icache_otp_key_q)
    )

    // Ensure that when a FENCE.I is executed, a new icache scramble key is requested.
    `ASSERT(IbexIcacheScrambleKeyRequestAfterFenceI_A,
        u_core.u_ibex_core.id_stage_i.instr_valid_i
        && u_core.u_ibex_core.id_stage_i.decoder_i.opcode == ibex_pkg::OPCODE_MISC_MEM
        && u_core.u_ibex_core.id_stage_i.decoder_i.instr[14:12] == 3'b001 // FENCE.I
        |-> ##[0:10] // upper bound is not exact, but it should not take more than a few cycles
        icache_otp_key_o.req
    )

  end

  `define ASSERT_IBEX_CORE_ERROR_TRIGGER_ALERT(__assert_name, __alert_name, _hier, __error_name)   \
    if (1) begin : g_``__error_name``_assert_signals                                               \
      logic __error_name;                                                                          \
      assign __error_name = u_core._hier``.__error_name;                                           \
                                                                                                   \
      logic unused_assert_connected;                                                               \
      `ASSERT_INIT_NET(AssertConnected_A, unused_assert_connected === 1'b1)                        \
    end                                                                                            \
    `ASSERT_ERROR_TRIGGER_ALERT(__assert_name, g_``__error_name``_assert_signals, __alert_name, 0, \
        30, // MAX_CYCLES_, use a large value as ibex clock is 4x faster than clk in alert_handler \
        __error_name)

  `ASSERT_IBEX_CORE_ERROR_TRIGGER_ALERT(IbexPcMismatchCheck_A, alert_tx_o[2],
      u_ibex_core.if_stage_i, pc_mismatch_alert_o)
  `ASSERT_IBEX_CORE_ERROR_TRIGGER_ALERT(IbexRfEccErrCheck_A, alert_tx_o[2], u_ibex_core,
      rf_ecc_err_comb)
  `ASSERT_IBEX_CORE_ERROR_TRIGGER_ALERT(IbexLoadRespIntgErrCheck_A, alert_tx_o[2], u_ibex_core,
      lsu_load_resp_intg_err)
  `ASSERT_IBEX_CORE_ERROR_TRIGGER_ALERT(IbexStoreRespIntgErrCheck_A, alert_tx_o[2], u_ibex_core,
      lsu_store_resp_intg_err)
  `ASSERT_IBEX_CORE_ERROR_TRIGGER_ALERT(IbexInstrIntgErrCheck_A, alert_tx_o[2], u_ibex_core,
      instr_intg_err)
`endif // ifdef INC_ASSERT
endmodule
