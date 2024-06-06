// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy distrubution network core module
//  - this module will make requests to the CSRNG module
//    and return the genbits back to up four requesting
//    end points.
//

`include "prim_assert.sv"

module edn_core import edn_pkg::*;
#(
  parameter int NumEndPoints = 4
) (
  input logic clk_i,
  input logic rst_ni,

  input  edn_reg_pkg::edn_reg2hw_t reg2hw,
  output edn_reg_pkg::edn_hw2reg_t hw2reg,

  // EDN interfaces
  input  edn_req_t [NumEndPoints-1:0] edn_i,
  output edn_rsp_t [NumEndPoints-1:0] edn_o,

  // CSRNG Application Interface
  output  csrng_pkg::csrng_req_t  csrng_cmd_o,
  input   csrng_pkg::csrng_rsp_t  csrng_cmd_i,

  // Alerts
  output logic        recov_alert_test_o,
  output logic        fatal_alert_test_o,
  output logic        recov_alert_o,
  output logic        fatal_alert_o,

  // Interrupts
  output logic        intr_edn_cmd_req_done_o,
  output logic        intr_edn_fatal_err_o
);

  import edn_reg_pkg::*;

  localparam int RegWidth = 32;
  localparam int RescmdFifoWidth = 32;
  localparam int RescmdFifoDepth = 13;
  localparam int GencmdFifoWidth = 32;
  localparam int GencmdFifoDepth = 13;
  localparam int CSGenBitsWidth = 128;
  localparam int EndPointBusWidth = 32;
  localparam int RescmdFifoIdxWidth = $clog2(RescmdFifoDepth);
  localparam int FifoRstCopies = 4;
  localparam int BootReqCopies = 2;

  typedef enum logic [4:0] {
    MuBiCheck,
    FatalErr,
    ReseedCmdErr,
    GenCmdErr,
    FifoWrErr,
    FifoRdErr,
    FifoStErr,
    CsrngCmdReq,
    CsrngCmdReqValid,
    CsrngCmdReqOut,
    CsrngCmdReqValidOut,
    SwCmdSts,
    HwCmdSts,
    MainFsmEn,
    CmdFifoCnt,
    CsrngPackerClr,
    CsrngFipsEn,
    CsrngDataVld,
    CsrngAckErr,
    AckFsmEn,
    LastEdnEntry
  } edn_enable_e;
  localparam int EdnEnableCopies = int'(LastEdnEntry);

  // signals
  logic event_edn_cmd_req_done;
  logic event_edn_fatal_err;
  logic event_edn_recov_err;
  logic [EdnEnableCopies-1:FatalErr] edn_enable_fo;
  logic [FifoRstCopies-1:1] cmd_fifo_rst_fo;
  logic [BootReqCopies-1:1] boot_req_mode_fo;
  logic edn_enable_pfa;
  logic cmd_fifo_rst_pfa;
  logic packer_arb_valid;
  logic packer_arb_ready;
  logic [NumEndPoints-1:0] packer_arb_req;
  logic [NumEndPoints-1:0] packer_arb_gnt;
  logic                    auto_req_mode_pfe;
  logic                    auto_req_mode_pfa;
  logic                    main_sm_done_pulse;
  logic                    capt_gencmd_fifo_cnt;
  logic                    capt_rescmd_fifo_cnt;
  logic                    max_reqs_cnt_zero;
  logic                    max_reqs_cnt_load;
  logic                    max_reqs_between_reseed_load;
  logic [31:0]             max_reqs_between_reseed_bus;
  logic                    send_rescmd, send_rescmd_gated;
  logic                    send_gencmd, send_gencmd_gated;
  logic                    cs_cmd_handshake, gencmd_handshake, rescmd_handshake;
  logic                    cs_hw_cmd_handshake;
  logic                    cs_hw_cmd_handshake_1st;
  logic                    main_sm_idle;
  logic                    cmd_sent;
  logic                    boot_wr_ins_cmd;
  logic                    boot_send_ins_cmd;
  logic                    boot_wr_gen_cmd;
  logic                    boot_wr_uni_cmd;
  logic                    sw_cmd_req_load;
  logic                    sw_cmd_mode;
  logic [31:0]             sw_cmd_req_bus;
  logic                    send_cs_cmd_gated;
  logic                    reseed_cmd_load;
  logic [31:0]             reseed_cmd_bus;
  logic                    generate_cmd_load;
  logic [31:0]             generate_cmd_bus;
  logic                    packer_cs_clr;
  logic                    packer_cs_push;
  logic [CSGenBitsWidth-1:0] packer_cs_wdata;
  logic                      packer_cs_wready;
  logic                      packer_cs_rvalid;
  logic                      packer_cs_rready;
  logic [CSGenBitsWidth-1:0] packer_cs_rdata;
  logic                      boot_req_mode_pfa;
  logic                      auto_req_mode_busy;
  logic                      accept_sw_cmds_pulse;

  logic [NumEndPoints-1:0]   packer_ep_clr;
  logic [NumEndPoints-1:0]   packer_ep_ack;
  logic [NumEndPoints-1:0]   packer_ep_push;
  logic [CSGenBitsWidth-1:0] packer_ep_wdata [NumEndPoints];
  logic [NumEndPoints-1:0]   packer_ep_wready;
  logic [NumEndPoints-1:0]   packer_ep_rvalid;
  logic [NumEndPoints-1:0]   packer_ep_rready;
  logic                      edn_ack_sm_err_sum;
  logic [NumEndPoints-1:0]   edn_ack_sm_err;
  logic [EndPointBusWidth-1:0] packer_ep_rdata [NumEndPoints];

  // rescmd fifo
  logic [RescmdFifoIdxWidth-1:0]      sfifo_rescmd_depth;
  logic [RescmdFifoWidth-1:0]         sfifo_rescmd_rdata;
  logic                               sfifo_rescmd_clr;
  logic                               sfifo_rescmd_push;
  logic [RescmdFifoWidth-1:0]         sfifo_rescmd_wdata;
  logic                               sfifo_rescmd_pop;
  logic                               sfifo_rescmd_err_sum;
  logic [2:0]                         sfifo_rescmd_err;
  logic                               sfifo_rescmd_full;
  logic                               sfifo_rescmd_not_empty;
  logic                               sfifo_rescmd_int_err;

  // gencmd fifo
  logic [GencmdFifoWidth-1:0]         sfifo_gencmd_rdata;
  logic [$clog2(GencmdFifoDepth)-1:0] sfifo_gencmd_depth;
  logic                               sfifo_gencmd_clr;
  logic                               sfifo_gencmd_push;
  logic [GencmdFifoWidth-1:0]         sfifo_gencmd_wdata;
  logic                               sfifo_gencmd_pop;
  logic                               sfifo_gencmd_err_sum;
  logic [2:0]                         sfifo_gencmd_err;
  logic                               sfifo_gencmd_full;
  logic                               sfifo_gencmd_not_empty;
  logic                               sfifo_gencmd_int_err;

  logic                               edn_main_sm_err_sum;
  logic [8:0]                         edn_main_sm_state;
  logic                               edn_main_sm_err;
  logic                               csrng_ack_err;
  logic                               reject_csrng_entropy;
  logic [30:0]                        err_code_test_bit;
  logic                               fifo_write_err_sum;
  logic                               fifo_read_err_sum;
  logic                               fifo_status_err_sum;
  logic                               cs_rdata_capt_vld;
  logic                               edn_bus_cmp_alert;
  logic                               edn_cntr_err_sum;
  logic                               edn_cntr_err;
  logic [RegWidth-1:0]                max_reqs_cnt;
  logic                               max_reqs_cnt_err;
  logic                               cmd_rdy;
  logic [31:0]                        boot_ins_cmd;
  logic [31:0]                        boot_gen_cmd;

  // unused
  logic                               unused_err_code_test_bit;

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_test_invalid;

  prim_mubi_pkg::mubi4_t [EdnEnableCopies-1:0] mubi_edn_enable_fanout;
  prim_mubi_pkg::mubi4_t [FifoRstCopies-1:0] mubi_cmd_fifo_rst_fanout;
  prim_mubi_pkg::mubi4_t [BootReqCopies-1:0] mubi_boot_req_mode_fanout;
  prim_mubi_pkg::mubi4_t [1:0] mubi_auto_req_mode_fanout;

  // flops
  logic [31:0]                        cs_cmd_req_q, cs_cmd_req_d;
  logic                               cs_cmd_req_vld_q, cs_cmd_req_vld_d;
  logic [31:0]                        cs_cmd_req_out_q, cs_cmd_req_out_d;
  logic                               cs_cmd_req_vld_out_q, cs_cmd_req_vld_out_d;
  logic                               cs_cmd_req_vld_hold_q, cs_cmd_req_vld_hold_d;
  logic [RescmdFifoIdxWidth-1:0]      cmd_fifo_cnt_q, cmd_fifo_cnt_d;
  logic                               csrng_fips_q, csrng_fips_d;
  logic [NumEndPoints-1:0]            edn_fips_q, edn_fips_d;
  logic [63:0]                        cs_rdata_capt_q, cs_rdata_capt_d;
  logic                               cs_rdata_capt_vld_q, cs_rdata_capt_vld_d;
  logic                               cmd_rdy_q, cmd_rdy_d;
  csrng_pkg::csrng_cmd_sts_e          csrng_cmd_sts_q, csrng_cmd_sts_d;
  logic                               csrng_sw_cmd_ack_q, csrng_sw_cmd_ack_d;
  logic                               csrng_hw_cmd_ack_q, csrng_hw_cmd_ack_d;
  csrng_pkg::csrng_cmd_sts_e          csrng_hw_cmd_sts_q, csrng_hw_cmd_sts_d;
  logic                               boot_mode_q, boot_mode_d,
                                      auto_mode_q, auto_mode_d;
  logic [3:0]                         cmd_type_q, cmd_type_d;
  logic                               cmd_reg_rdy_d, cmd_reg_rdy_q;
  logic                               cmd_hdr_busy_d, cmd_hdr_busy_q;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      cs_cmd_req_q  <= '0;
      cs_cmd_req_vld_q  <= '0;
      cs_cmd_req_out_q  <= '0;
      cs_cmd_req_vld_out_q  <= '0;
      cs_cmd_req_vld_hold_q <= '0;
      cmd_fifo_cnt_q <= '0;
      csrng_fips_q <= '0;
      edn_fips_q <= '0;
      cs_rdata_capt_q <= '0;
      cs_rdata_capt_vld_q <= '0;
      cmd_rdy_q   <= '0;
      csrng_cmd_sts_q   <= csrng_pkg::CMD_STS_SUCCESS;
      csrng_sw_cmd_ack_q   <= '0;
      csrng_hw_cmd_sts_q   <= csrng_pkg::CMD_STS_SUCCESS;
      boot_mode_q   <= '0;
      auto_mode_q   <= '0;
      cmd_type_q   <= {1'b0, csrng_pkg::INV};
      cmd_reg_rdy_q   <= '0;
      cmd_hdr_busy_q <= 1'b0;
    end else begin
      cs_cmd_req_q  <= cs_cmd_req_d;
      cs_cmd_req_vld_q  <= cs_cmd_req_vld_d;
      cs_cmd_req_out_q <= cs_cmd_req_out_d;
      cs_cmd_req_vld_out_q <= cs_cmd_req_vld_out_d;
      cs_cmd_req_vld_hold_q <= cs_cmd_req_vld_hold_d;
      cmd_fifo_cnt_q <= cmd_fifo_cnt_d;
      csrng_fips_q <= csrng_fips_d;
      edn_fips_q <= edn_fips_d;
      cs_rdata_capt_q <= cs_rdata_capt_d;
      cs_rdata_capt_vld_q <= cs_rdata_capt_vld_d;
      cmd_rdy_q   <= cmd_rdy_d;
      csrng_cmd_sts_q   <= csrng_cmd_sts_d;
      csrng_sw_cmd_ack_q   <= csrng_sw_cmd_ack_d;
      csrng_hw_cmd_ack_q   <= csrng_hw_cmd_ack_d;
      csrng_hw_cmd_sts_q   <= csrng_hw_cmd_sts_d;
      boot_mode_q   <= boot_mode_d;
      auto_mode_q   <= auto_mode_d;
      cmd_type_q   <= cmd_type_d;
      cmd_reg_rdy_q   <= cmd_reg_rdy_d;
      cmd_hdr_busy_q <= cmd_hdr_busy_d;
    end

  //--------------------------------------------
  // instantiate interrupt hardware primitives
  //--------------------------------------------

  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_edn_cmd_req_done (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_edn_cmd_req_done),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.edn_cmd_req_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.edn_cmd_req_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.edn_cmd_req_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.edn_cmd_req_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.edn_cmd_req_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.edn_cmd_req_done.d),
    .intr_o                 (intr_edn_cmd_req_done_o)
  );


  prim_intr_hw #(
    .Width(1)
  ) u_intr_hw_edn_fatal_err (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_edn_fatal_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.edn_fatal_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.edn_fatal_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.edn_fatal_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.edn_fatal_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.edn_fatal_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.edn_fatal_err.d),
    .intr_o                 (intr_edn_fatal_err_o)
  );

  // interrupt for sw app interface only
  assign event_edn_cmd_req_done = csrng_cmd_i.csrng_rsp_ack && sw_cmd_mode;

  // Counter, internal FIFO errors and FSM errors are structural errors and are always active
  // regardless of the functional state.
  logic fatal_loc_events;
  assign fatal_loc_events =  sfifo_rescmd_int_err ||
                             sfifo_gencmd_int_err ||
                             edn_cntr_err_sum ||
                             edn_main_sm_err_sum ||
                             edn_ack_sm_err_sum;

  // set the interrupt sources
  assign event_edn_fatal_err = (edn_enable_fo[FatalErr] && (
         sfifo_rescmd_err_sum ||
         sfifo_gencmd_err_sum )) ||
         fatal_loc_events;

  // set fifo errors that are single instances of source
  assign sfifo_rescmd_err_sum = (|sfifo_rescmd_err) ||
         err_code_test_bit[0];
  assign sfifo_gencmd_err_sum = (|sfifo_gencmd_err) ||
         err_code_test_bit[1];
  assign edn_ack_sm_err_sum = (|edn_ack_sm_err) ||
         err_code_test_bit[20];
  assign edn_main_sm_err_sum = edn_main_sm_err ||
         err_code_test_bit[21];
  assign edn_cntr_err_sum = edn_cntr_err ||
         err_code_test_bit[22];

  assign fifo_write_err_sum =
         sfifo_rescmd_err[2] ||
         sfifo_gencmd_err[2] ||
         err_code_test_bit[28];
  assign fifo_read_err_sum =
         sfifo_rescmd_err[1] ||
         sfifo_gencmd_err[1] ||
         err_code_test_bit[29];
  assign fifo_status_err_sum =
         sfifo_rescmd_err[0] ||
         sfifo_gencmd_err[0] ||
         err_code_test_bit[30];


  // set the err code source bits
  assign hw2reg.err_code.sfifo_rescmd_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_rescmd_err.de = edn_enable_fo[ReseedCmdErr] && sfifo_rescmd_err_sum;

  assign hw2reg.err_code.sfifo_gencmd_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_gencmd_err.de = edn_enable_fo[GenCmdErr] && sfifo_gencmd_err_sum;

  assign hw2reg.err_code.edn_ack_sm_err.d = 1'b1;
  assign hw2reg.err_code.edn_ack_sm_err.de = edn_ack_sm_err_sum;

  assign hw2reg.err_code.edn_main_sm_err.d = 1'b1;
  assign hw2reg.err_code.edn_main_sm_err.de = edn_main_sm_err_sum;

  assign hw2reg.err_code.edn_cntr_err.d = 1'b1;
  assign hw2reg.err_code.edn_cntr_err.de = edn_cntr_err_sum;

  assign boot_ins_cmd = reg2hw.boot_ins_cmd.q;
  assign boot_gen_cmd = reg2hw.boot_gen_cmd.q;


 // set the err code type bits
  assign hw2reg.err_code.fifo_write_err.d = 1'b1;
  assign hw2reg.err_code.fifo_write_err.de = edn_enable_fo[FifoWrErr] && fifo_write_err_sum;

  assign hw2reg.err_code.fifo_read_err.d = 1'b1;
  assign hw2reg.err_code.fifo_read_err.de = edn_enable_fo[FifoRdErr] && fifo_read_err_sum;

  assign hw2reg.err_code.fifo_state_err.d = 1'b1;
  assign hw2reg.err_code.fifo_state_err.de = edn_enable_fo[FifoStErr] && fifo_status_err_sum;


  // Error forcing
  for (genvar i = 0; i < 31; i = i+1) begin : gen_err_code_test_bit
    assign err_code_test_bit[i] = (reg2hw.err_code_test.q == i) && reg2hw.err_code_test.qe;
  end : gen_err_code_test_bit

  // CSRNG acknowledgement error status
  assign csrng_ack_err = edn_enable_fo[CsrngAckErr] &&
      csrng_cmd_i.csrng_rsp_ack && (csrng_cmd_i.csrng_rsp_sts != csrng_pkg::CMD_STS_SUCCESS);
  assign hw2reg.recov_alert_sts.csrng_ack_err.de = csrng_ack_err;
  assign hw2reg.recov_alert_sts.csrng_ack_err.d  = csrng_ack_err;

  // Combine all recoverable alert signals into one singular signal.
  assign event_edn_recov_err = edn_bus_cmp_alert || cmd_fifo_rst_pfa || auto_req_mode_pfa ||
                               boot_req_mode_pfa || edn_enable_pfa || csrng_ack_err;

  // Turn event_edn_recov_err into a pulse for the case when
  // the signals are high for more then one cycle.
  prim_edge_detector #(
    .Width(1),
    .ResetValue(0),
    .EnSync(0)
  ) u_prim_edge_detector_recov_alert (
    .clk_i,
    .rst_ni,
    .d_i(event_edn_recov_err),
    .q_sync_o(),
    .q_posedge_pulse_o(recov_alert_o),
    .q_negedge_pulse_o()
  );

  // alert - send all interrupt sources to the alert for the fatal case
  assign fatal_alert_o = event_edn_fatal_err || sfifo_rescmd_int_err || sfifo_gencmd_int_err;

  // alert test
  assign recov_alert_test_o = {
    reg2hw.alert_test.recov_alert.q &&
    reg2hw.alert_test.recov_alert.qe
  };
  assign fatal_alert_test_o = {
    reg2hw.alert_test.fatal_alert.q &&
    reg2hw.alert_test.fatal_alert.qe
  };

  // check for illegal enable field states, and set alert if detected

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_edn_enable;
  assign mubi_edn_enable = mubi4_t'(reg2hw.ctrl.edn_enable.q);
  assign edn_enable_pfa = mubi4_test_invalid(mubi_edn_enable_fanout[MuBiCheck]);
  assign hw2reg.recov_alert_sts.edn_enable_field_alert.de = edn_enable_pfa;
  assign hw2reg.recov_alert_sts.edn_enable_field_alert.d  = edn_enable_pfa;

  for (genvar i = int'(FatalErr); i < LastEdnEntry; i = i+1) begin : gen_mubi_en_copies
    assign edn_enable_fo[i] = mubi4_test_true_strict(mubi_edn_enable_fanout[i]);
  end : gen_mubi_en_copies

  prim_mubi4_sync #(
    .NumCopies(EdnEnableCopies),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_edn_enable (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_edn_enable),
    .mubi_o(mubi_edn_enable_fanout)
  );

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_cmd_fifo_rst;
  assign mubi_cmd_fifo_rst = mubi4_t'(reg2hw.ctrl.cmd_fifo_rst.q);
  assign cmd_fifo_rst_pfa = mubi4_test_invalid(mubi_cmd_fifo_rst_fanout[0]);
  assign hw2reg.recov_alert_sts.cmd_fifo_rst_field_alert.de = cmd_fifo_rst_pfa;
  assign hw2reg.recov_alert_sts.cmd_fifo_rst_field_alert.d  = cmd_fifo_rst_pfa;

  for (genvar i = 1; i < FifoRstCopies; i = i+1) begin : gen_mubi_rst_copies
    assign cmd_fifo_rst_fo[i] = mubi4_test_true_strict(mubi_cmd_fifo_rst_fanout[i]);
  end : gen_mubi_rst_copies

  prim_mubi4_sync #(
    .NumCopies(FifoRstCopies),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_cmd_fifo_rst (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_cmd_fifo_rst),
    .mubi_o(mubi_cmd_fifo_rst_fanout)
  );

  // counter errors
  assign edn_cntr_err = max_reqs_cnt_err;

  //--------------------------------------------
  // sw register interface
  //--------------------------------------------
  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_auto_req_mode;
  assign mubi_auto_req_mode = mubi4_t'(reg2hw.ctrl.auto_req_mode.q);
  assign auto_req_mode_pfe = mubi4_test_true_strict(mubi_auto_req_mode_fanout[0]);
  assign auto_req_mode_pfa = mubi4_test_invalid(mubi_auto_req_mode_fanout[1]);
  assign hw2reg.recov_alert_sts.auto_req_mode_field_alert.de = auto_req_mode_pfa;
  assign hw2reg.recov_alert_sts.auto_req_mode_field_alert.d  = auto_req_mode_pfa;

  prim_mubi4_sync #(
    .NumCopies(2),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_auto_req_mode (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_auto_req_mode),
    .mubi_o(mubi_auto_req_mode_fanout)
  );


  // SW interface connection
  // cmd req
  assign sw_cmd_req_load = reg2hw.sw_cmd_req.qe && cmd_reg_rdy_q;
  assign sw_cmd_req_bus = reg2hw.sw_cmd_req.q;

  assign max_reqs_between_reseed_load = reg2hw.max_num_reqs_between_reseeds.qe;
  assign max_reqs_between_reseed_bus = reg2hw.max_num_reqs_between_reseeds.q;

  assign reseed_cmd_load = reg2hw.reseed_cmd.qe;
  assign reseed_cmd_bus = reg2hw.reseed_cmd.q;

  assign generate_cmd_load = reg2hw.generate_cmd.qe;
  assign generate_cmd_bus = reg2hw.generate_cmd.q;

  assign cs_cmd_handshake = cs_cmd_req_vld_out_q && send_cs_cmd_gated;
  assign gencmd_handshake = cs_cmd_req_vld_out_q && send_gencmd_gated;
  assign rescmd_handshake = cs_cmd_req_vld_out_q && send_rescmd_gated;

  // The cs_cmd_req register feeds commands from the EDN TL-UL registers to the output register.
  assign cs_cmd_req_d =
         (!edn_enable_fo[CsrngCmdReq]) ? '0 :
         boot_wr_ins_cmd ? boot_ins_cmd :
         boot_wr_gen_cmd ? boot_gen_cmd :
         boot_wr_uni_cmd ? edn_pkg::BOOT_UNINSTANTIATE :
         sw_cmd_req_load ? sw_cmd_req_bus :
         cs_cmd_req_q;

  // The cs_cmd_req_vld register handles the valid signal that is sent along with cs_cmd_req_q.
  assign cs_cmd_req_vld_d =
         (!edn_enable_fo[CsrngCmdReqValid]) ? '0 :
         cs_cmd_handshake ? '0 :
         (sw_cmd_req_load || boot_wr_ins_cmd ||
          boot_wr_gen_cmd || boot_wr_uni_cmd) ? 1'b1 :
         cs_cmd_req_vld_q; // cmd reg write

  assign send_cs_cmd_gated = cs_cmd_req_vld_q && csrng_cmd_i.csrng_req_ready;

  // The cs_cmd_req_out register feeds the commands coming from the auto mode FIFOs
  // or the cs_cmd_req register to the CSRNG.
  assign cs_cmd_req_out_d =
         (!edn_enable_fo[CsrngCmdReqOut]) ? '0 :
         // Update the output value with the next word of the reseed command in auto mode.
         (send_rescmd || capt_rescmd_fifo_cnt) ? (sfifo_rescmd_pop ?
                                                  sfifo_rescmd_rdata :
                                                  cs_cmd_req_out_q) :
         // Update the output value with the next word of the generate command in auto mode.
         (send_gencmd || capt_gencmd_fifo_cnt) ? (sfifo_gencmd_pop ?
                                                  sfifo_gencmd_rdata :
                                                  cs_cmd_req_out_q) :
         // Update the output value with the next word of the cs_cmd_req register.
         (cs_cmd_req_vld_q && !cs_cmd_handshake) ? cs_cmd_req_q :
         cs_cmd_req_out_q;

  // Hold the valid until completing the valid/ready handshake. This is required to not violate
  // the valid/ready protocol in case of acknowledgement errors received from CSRNG.
  assign cs_cmd_req_vld_hold_d =
         (!edn_enable_fo[CsrngCmdReqValidOut]) ? 1'b0 :
         (cs_cmd_req_vld_hold_q || cs_cmd_req_vld_out_q) && !csrng_cmd_i.csrng_req_ready;

  // The cs_cmd_req_vld_out register handles the valid signal that is sent along with
  // cs_cmd_req_out. Unless EDN is disabled, the valid must not be dropped before seeing the
  // ready.
  assign cs_cmd_req_vld_out_d =
         (!edn_enable_fo[CsrngCmdReqValidOut]) ? '0 :
         cmd_sent ? '0 :
         (send_rescmd || capt_rescmd_fifo_cnt) ? 1'b1 :
         (send_gencmd || capt_gencmd_fifo_cnt) ? 1'b1 :
         cs_cmd_req_vld_q && !cs_cmd_handshake;

  // drive outputs
  assign csrng_cmd_o.csrng_req_valid =
         (cs_cmd_req_vld_out_q && !reject_csrng_entropy) || cs_cmd_req_vld_hold_q;
  assign csrng_cmd_o.csrng_req_bus = cs_cmd_req_out_q;

  // Accept a new command only if no command is currently being written to SW_CMD_REQ
  // and the register is ready for the next word.
  assign hw2reg.sw_cmd_sts.cmd_rdy.de = 1'b1;
  assign hw2reg.sw_cmd_sts.cmd_rdy.d = cmd_rdy;
  assign cmd_rdy = !sw_cmd_req_load && cmd_rdy_d && cmd_reg_rdy_d;
  // We accept SW commands only in SW or auto mode.
  // In auto mode, sw_cmd_mode will transition to low after the initial instantiate command.
  // In SW mode, cmd_rdy is low when a previous command has not been acked yet.
  assign cmd_rdy_d =
         !edn_enable_fo[SwCmdSts] ? 1'b0 :
         !sw_cmd_mode ? 1'b0 :
         reject_csrng_entropy ? 1'b0 :
         sw_cmd_req_load ? 1'b0 :
         accept_sw_cmds_pulse ? 1'b1 :
         csrng_cmd_i.csrng_rsp_ack ? 1'b1 :
         cmd_rdy_q;

  // cmd_reg_rdy_d is high if SW_CMD_REQ is ready to accept a new word.
  assign hw2reg.sw_cmd_sts.cmd_reg_rdy.de = 1'b1;
  assign hw2reg.sw_cmd_sts.cmd_reg_rdy.d = cmd_reg_rdy_d;
  assign cmd_reg_rdy_d =
         !edn_enable_fo[SwCmdSts] ? 1'b0 :
         !sw_cmd_mode ? 1'b0 :
         reject_csrng_entropy ? 1'b0 :
         sw_cmd_req_load ? 1'b0 :
         accept_sw_cmds_pulse ? 1'b1 :
         cs_cmd_handshake ? 1'b1 :
         cmd_reg_rdy_q;

  // Whenever a sw_cmd_req is acked by CSRNG, update the command status.
  assign hw2reg.sw_cmd_sts.cmd_sts.de = 1'b1;
  assign hw2reg.sw_cmd_sts.cmd_sts.d = csrng_cmd_sts_d;
  assign csrng_cmd_sts_d =
         !edn_enable_fo[SwCmdSts] ? csrng_pkg::CMD_STS_SUCCESS :
         csrng_cmd_i.csrng_rsp_ack && sw_cmd_mode &&
            !reject_csrng_entropy ? csrng_cmd_i.csrng_rsp_sts :
         csrng_cmd_sts_q;

  // cmd_ack goes high only when a command is acknowledged that has been loaded into sw_cmd_req.
  assign hw2reg.sw_cmd_sts.cmd_ack.de = 1'b1;
  assign hw2reg.sw_cmd_sts.cmd_ack.d = csrng_sw_cmd_ack_d;
  assign csrng_sw_cmd_ack_d =
         !edn_enable_fo[SwCmdSts] ? 1'b0 :
         sw_cmd_req_load ? 1'b0 :
         csrng_cmd_i.csrng_rsp_ack && sw_cmd_mode && !reject_csrng_entropy ? 1'b1 :
         csrng_sw_cmd_ack_q;

  //--------------------------------------------
  // hw_cmd_sts register
  //--------------------------------------------
  assign main_sm_idle = (edn_main_sm_state == Idle);
  assign cs_hw_cmd_handshake = !sw_cmd_mode && csrng_cmd_o.csrng_req_valid &&
                               csrng_cmd_i.csrng_req_ready;
  assign cs_hw_cmd_handshake_1st = cs_hw_cmd_handshake &&
                                   ((send_rescmd || capt_rescmd_fifo_cnt ||
                                     send_gencmd || capt_gencmd_fifo_cnt) ? cmd_hdr_busy_q : 1'b1);

  // Set the boot_mode field to one when boot mode is entered and to zero when it is left.
  assign hw2reg.hw_cmd_sts.boot_mode.de = 1'b1;
  assign hw2reg.hw_cmd_sts.boot_mode.d = boot_mode_d;
  assign boot_mode_d = main_sm_done_pulse || main_sm_idle ? 1'b0 :
                       boot_send_ins_cmd && cs_hw_cmd_handshake ? 1'b1 :
                       boot_mode_q;
  // Set the auto_mode field to one when auto mode is entered and to zero when it is left. In case
  // the first handshake in automode leads to an error, we still set the auto_mode field to know
  // that the error happened upon entering auto mode.
  assign hw2reg.hw_cmd_sts.auto_mode.de = 1'b1;
  assign hw2reg.hw_cmd_sts.auto_mode.d = auto_mode_d;
  assign auto_mode_d = main_sm_done_pulse || main_sm_idle ? 1'b0 :
                       auto_req_mode_busy && cs_hw_cmd_handshake ? 1'b1 :
                       auto_mode_q;
  // Record the cmd_sts signal each time a hardware command is acknowledged.
  // Reset it each time a new hardware command is issued. In case we saw an error previously,
  // keep status returned with the error.
  assign hw2reg.hw_cmd_sts.cmd_sts.de = 1'b1;
  assign hw2reg.hw_cmd_sts.cmd_sts.d = csrng_hw_cmd_sts_d;
  assign csrng_hw_cmd_sts_d =
         !edn_enable_fo[HwCmdSts] ? csrng_pkg::CMD_STS_SUCCESS :
         csrng_cmd_i.csrng_rsp_ack && !sw_cmd_mode &&
            !reject_csrng_entropy ? csrng_cmd_i.csrng_rsp_sts :
         reject_csrng_entropy ? csrng_hw_cmd_sts_q :
         cs_hw_cmd_handshake ? csrng_pkg::CMD_STS_SUCCESS :
         csrng_hw_cmd_sts_q;
  // Set the cmd_ack signal to high whenever a hardware command is acknowledged and set it
  // to low whenever a new hardware command is issued to the CSRNG. Don't clear it in case we saw
  // an error previously.
  assign hw2reg.hw_cmd_sts.cmd_ack.de = 1'b1;
  assign hw2reg.hw_cmd_sts.cmd_ack.d = csrng_hw_cmd_ack_d;
  assign csrng_hw_cmd_ack_d =
         !edn_enable_fo[HwCmdSts] ? 1'b0 :
         csrng_cmd_i.csrng_rsp_ack && !sw_cmd_mode && !reject_csrng_entropy ? 1'b1 :
         reject_csrng_entropy ? csrng_hw_cmd_ack_q :
         cs_hw_cmd_handshake ? 1'b0 :
         csrng_hw_cmd_ack_q;
  // Set the cmd_type to the application command type value of the hardware controlled
  // command issued last. Only the command header but not the additional data matters.
  // Don't update it in case we saw an error previously.
  assign hw2reg.hw_cmd_sts.cmd_type.de = 1'b1;
  assign hw2reg.hw_cmd_sts.cmd_type.d = cmd_type_d;
  assign cmd_type_d =
         !edn_enable_fo[HwCmdSts] ? {1'b0, csrng_pkg::INV} :
         reject_csrng_entropy ? cmd_type_q :
         cs_hw_cmd_handshake_1st ? cs_cmd_req_out_q[3:0] : cmd_type_q;

  // rescmd fifo
  // SEC_CM: FIFO.CTR.REDUN
  prim_fifo_sync #(
    .Width(RescmdFifoWidth),
    .Pass(0),
    .Depth(RescmdFifoDepth),
    .OutputZeroIfEmpty(0),
    .Secure(1)
  ) u_prim_fifo_sync_rescmd (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .clr_i    (sfifo_rescmd_clr),
    .wvalid_i (sfifo_rescmd_push),
    .wready_o (),
    .wdata_i  (sfifo_rescmd_wdata),
    .rvalid_o (sfifo_rescmd_not_empty),
    .rready_i (sfifo_rescmd_pop),
    .rdata_o  (sfifo_rescmd_rdata),
    .full_o   (sfifo_rescmd_full),
    .depth_o  (sfifo_rescmd_depth),
    .err_o    (sfifo_rescmd_int_err)
  );

  // Gate rescmd FIFO operations in case of CSRNG backpressure.
  assign send_rescmd_gated = (send_rescmd || capt_rescmd_fifo_cnt) && csrng_cmd_i.csrng_req_ready;

  assign sfifo_rescmd_push =
         rescmd_handshake ? 1'b1  :
         reseed_cmd_load;

  assign sfifo_rescmd_wdata =
         auto_req_mode_busy ? cs_cmd_req_out_q :
         reseed_cmd_bus;

  assign sfifo_rescmd_pop = (rescmd_handshake && !cmd_sent) || capt_rescmd_fifo_cnt;

  assign sfifo_rescmd_clr = (cmd_fifo_rst_fo[1] || main_sm_done_pulse);

  assign sfifo_rescmd_err =
         {(sfifo_rescmd_push && sfifo_rescmd_full),
          (sfifo_rescmd_pop && !sfifo_rescmd_not_empty),
          (sfifo_rescmd_full && !sfifo_rescmd_not_empty) || sfifo_rescmd_int_err};

  // gencmd fifo
  // SEC_CM: FIFO.CTR.REDUN
  prim_fifo_sync #(
    .Width(GencmdFifoWidth),
    .Pass(0),
    .Depth(GencmdFifoDepth),
    .OutputZeroIfEmpty(0),
    .Secure(1)
  ) u_prim_fifo_sync_gencmd (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .clr_i    (sfifo_gencmd_clr),
    .wvalid_i (sfifo_gencmd_push),
    .wready_o (),
    .wdata_i  (sfifo_gencmd_wdata),
    .rvalid_o (sfifo_gencmd_not_empty),
    .rready_i (sfifo_gencmd_pop),
    .rdata_o  (sfifo_gencmd_rdata),
    .full_o   (sfifo_gencmd_full),
    .depth_o  (sfifo_gencmd_depth),
    .err_o    (sfifo_gencmd_int_err)
  );

  // Gate gencmd FIFO operations in case of CSRNG backpressure.
  assign send_gencmd_gated = (send_gencmd || capt_gencmd_fifo_cnt) && csrng_cmd_i.csrng_req_ready;

  assign sfifo_gencmd_push =
         gencmd_handshake ? 1'b1 :
         generate_cmd_load;

  assign sfifo_gencmd_wdata =
         auto_req_mode_busy ? cs_cmd_req_out_q :
         generate_cmd_bus;

  assign sfifo_gencmd_pop = (gencmd_handshake && !cmd_sent) || capt_gencmd_fifo_cnt;

  assign sfifo_gencmd_clr = (cmd_fifo_rst_fo[2] || main_sm_done_pulse);

  assign sfifo_gencmd_err =
         {(sfifo_gencmd_push && sfifo_gencmd_full),
          (sfifo_gencmd_pop && !sfifo_gencmd_not_empty),
          (sfifo_gencmd_full && !sfifo_gencmd_not_empty) || sfifo_gencmd_int_err};

  // sm to process csrng commands
  // SEC_CM: MAIN_SM.FSM.SPARSE
  // SEC_CM: MAIN_SM.CTR.LOCAL_ESC
  edn_main_sm u_edn_main_sm (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .edn_enable_i           (edn_enable_fo[MainFsmEn]),
    .boot_req_mode_i        (boot_req_mode_fo[1]),
    .auto_req_mode_i        (auto_req_mode_pfe),
    .sw_cmd_req_load_i      (sw_cmd_req_load),
    .sw_cmd_mode_o          (sw_cmd_mode),
    .boot_wr_ins_cmd_o      (boot_wr_ins_cmd),
    .boot_send_ins_cmd_o    (boot_send_ins_cmd),
    .boot_wr_gen_cmd_o      (boot_wr_gen_cmd),
    .boot_wr_uni_cmd_o      (boot_wr_uni_cmd),
    .accept_sw_cmds_pulse_o (accept_sw_cmds_pulse),
    .main_sm_done_pulse_o   (main_sm_done_pulse),
    .csrng_cmd_ack_i        (csrng_cmd_i.csrng_rsp_ack),
    .capt_gencmd_fifo_cnt_o (capt_gencmd_fifo_cnt),
    .send_gencmd_o          (send_gencmd),
    .max_reqs_cnt_zero_i    (max_reqs_cnt_zero),
    .capt_rescmd_fifo_cnt_o (capt_rescmd_fifo_cnt),
    .send_rescmd_o          (send_rescmd),
    .cmd_sent_i             (cmd_sent),
    .auto_req_mode_busy_o   (auto_req_mode_busy),
    .main_sm_state_o        (edn_main_sm_state),
    .csrng_ack_err_i        (csrng_ack_err),
    .reject_csrng_entropy_o (reject_csrng_entropy),
    .local_escalate_i       (fatal_loc_events),
    .main_sm_err_o          (edn_main_sm_err)
  );


  // Maximum requests counter for a generate command

  // SEC_CM: CTR.REDUN
  prim_count #(
    .Width(RegWidth),
    .ResetValue(edn_reg_pkg::MaxNumReqsBetweenReseedsResval)
  ) u_prim_count_max_reqs_cntr (
    .clk_i,
    .rst_ni,
    .clr_i(1'b0),
    .set_i(max_reqs_cnt_load),
    .set_cnt_i(max_reqs_between_reseed_bus),
    .incr_en_i(1'b0),
    .decr_en_i(send_gencmd && cmd_sent), // count down
    .step_i(RegWidth'(1)),
    .commit_i(1'b1),
    .cnt_o(max_reqs_cnt),
    .cnt_after_commit_o(),
    .err_o(max_reqs_cnt_err)
  );


  assign max_reqs_cnt_load = (max_reqs_between_reseed_load || // sw initial load
                              send_rescmd && cmd_sent ||      // runtime decrement
                              main_sm_done_pulse);            // restore when auto mode done

  assign max_reqs_cnt_zero = (max_reqs_cnt == '0);


  assign cmd_fifo_cnt_d =
         (!edn_enable_fo[CmdFifoCnt]) ? '0 :
         (cmd_fifo_rst_fo[3] || main_sm_done_pulse) ? '0 :
         capt_gencmd_fifo_cnt ? sfifo_gencmd_depth :
         capt_rescmd_fifo_cnt ? sfifo_rescmd_depth :
         (sfifo_gencmd_pop || sfifo_rescmd_pop) ? (cmd_fifo_cnt_q-1) :
         cmd_fifo_cnt_q;

  // Consider a reseed command as sent if all values have been popped from the queue once
  // and the handshake with CSRNG happend for the last word.
  assign cmd_sent = (cmd_fifo_cnt_q == RescmdFifoIdxWidth'(1)) &&
                    (gencmd_handshake || rescmd_handshake);

  // Track whether we're currently sending the command header of a hardware Reseed or Generate
  // command.
  assign cmd_hdr_busy_d =
      capt_gencmd_fifo_cnt || capt_rescmd_fifo_cnt ? 1'b1 :
      cs_hw_cmd_handshake                          ? 1'b0 : cmd_hdr_busy_q;

  // SEC_CM: CONFIG.MUBI
  mubi4_t mubi_boot_req_mode;
  assign mubi_boot_req_mode = mubi4_t'(reg2hw.ctrl.boot_req_mode.q);
  assign boot_req_mode_pfa = mubi4_test_invalid(mubi_boot_req_mode_fanout[0]);
  assign hw2reg.recov_alert_sts.boot_req_mode_field_alert.de = boot_req_mode_pfa;
  assign hw2reg.recov_alert_sts.boot_req_mode_field_alert.d  = boot_req_mode_pfa;

  for (genvar i = 1; i < BootReqCopies; i = i+1) begin : gen_mubi_boot_copies
    assign boot_req_mode_fo[i] = mubi4_test_true_strict(mubi_boot_req_mode_fanout[i]);
  end : gen_mubi_boot_copies

  prim_mubi4_sync #(
    .NumCopies(BootReqCopies),
    .AsyncOn(0)
  ) u_prim_mubi4_sync_boot_req_mode (
    .clk_i,
    .rst_ni,
    .mubi_i(mubi_boot_req_mode),
    .mubi_o(mubi_boot_req_mode_fanout)
  );


  //--------------------------------------------
  // packer arbitration
  //--------------------------------------------

  prim_arbiter_ppc #(
    .EnDataPort(0),    // Ignore data port
    .N(NumEndPoints),  // Number of request ports
    .DW(1)  // Data width
  ) u_prim_arbiter_ppc_packer_arb (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .req_chk_i(1'b1),
    .req_i(packer_arb_req), // N number of reqs
    .data_i('{default: 1'b0}),
    .gnt_o(packer_arb_gnt), // N number of gnts
    .idx_o(), //NC
    .valid_o(packer_arb_valid),
    .data_o(), // NC
    .ready_i(packer_arb_ready)
  );

  for (genvar i = 0; i < NumEndPoints; i=i+1) begin : gen_arb
    assign packer_arb_req[i] = !packer_ep_rvalid[i] && edn_i[i].edn_req;
  end

  //--------------------------------------------
  // csrng interface packer
  //--------------------------------------------

  prim_packer_fifo #(
     .InW(CSGenBitsWidth),
     .OutW(CSGenBitsWidth),
     .ClearOnRead(1'b0)
  ) u_prim_packer_fifo_cs (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .clr_i      (packer_cs_clr),
    .wvalid_i   (packer_cs_push),
    .wdata_i    (packer_cs_wdata),
    .wready_o   (packer_cs_wready),
    .rvalid_o   (packer_cs_rvalid),
    .rdata_o    (packer_cs_rdata),
    .rready_i   (packer_cs_rready),
    .depth_o    ()
  );

  assign packer_cs_clr = !edn_enable_fo[CsrngPackerClr];
  assign packer_cs_push = csrng_cmd_i.genbits_valid && !reject_csrng_entropy &&
                          !((csrng_cmd_i.csrng_rsp_sts != csrng_pkg::CMD_STS_SUCCESS) &&
                              csrng_cmd_i.csrng_rsp_ack);
  assign packer_cs_wdata = csrng_cmd_i.genbits_bus;
  assign csrng_cmd_o.genbits_ready = packer_cs_wready && !reject_csrng_entropy;
  assign packer_cs_rready = packer_arb_valid;
  assign packer_arb_ready = packer_cs_rvalid;

  assign csrng_fips_d =
         !edn_enable_fo[CsrngFipsEn] ? 1'b0 :
         (packer_cs_push && packer_cs_wready) ? csrng_cmd_i.genbits_fips :
         csrng_fips_q;

  //--------------------------------------------
  // data path integrity check
  // - a counter measure to software genbits bus tampering
  // - checks to make sure repeated data sets off
  //   an alert for sw to handle
  //--------------------------------------------

  // SEC_CM: CS_RDATA.BUS.CONSISTENCY

  // capture a copy of the entropy data
  assign cs_rdata_capt_vld = (packer_cs_rvalid && packer_cs_rready);

  assign cs_rdata_capt_d = cs_rdata_capt_vld ? packer_cs_rdata[63:0] : cs_rdata_capt_q;

  assign cs_rdata_capt_vld_d =
         !edn_enable_fo[CsrngDataVld] ? 1'b0 :
         cs_rdata_capt_vld ? 1'b1 :
         cs_rdata_capt_vld_q;

  // continuous compare of the entropy data
  assign edn_bus_cmp_alert = cs_rdata_capt_vld && cs_rdata_capt_vld_q &&
         (cs_rdata_capt_q == packer_cs_rdata[63:0]);

  assign hw2reg.recov_alert_sts.edn_bus_cmp_alert.de = edn_bus_cmp_alert;
  assign hw2reg.recov_alert_sts.edn_bus_cmp_alert.d  = edn_bus_cmp_alert;

  //--------------------------------------------
  // end point interface packers generation
  //--------------------------------------------

  for (genvar i = 0; i < NumEndPoints; i=i+1) begin : gen_ep_blk
    prim_packer_fifo #(
      .InW(CSGenBitsWidth),
      .OutW(EndPointBusWidth),
      .ClearOnRead(1'b0)
    ) u_prim_packer_fifo_ep (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .clr_i      (packer_ep_clr[i]),
      .wvalid_i   (packer_ep_push[i]),
      .wdata_i    (packer_ep_wdata[i]),
      .wready_o   (packer_ep_wready[i]),
      .rvalid_o   (packer_ep_rvalid[i]),
      .rdata_o    (packer_ep_rdata[i]),
      .rready_i   (packer_ep_rready[i]),
      .depth_o    ()
    );

    assign packer_ep_push[i] = packer_arb_valid && packer_ep_wready[i] && packer_arb_gnt[i];
    assign packer_ep_wdata[i] = packer_cs_rdata;

    // fips indication
    assign edn_fips_d[i] = packer_ep_clr[i] ? 1'b0 :
           (packer_ep_push[i] && packer_ep_wready[i]) ?  csrng_fips_q :
           edn_fips_q[i];
    assign edn_o[i].edn_fips = edn_fips_q[i];

    // gate returned data
    assign edn_o[i].edn_ack = packer_ep_ack[i];
    assign edn_o[i].edn_bus = packer_ep_rdata[i];

  // SEC_CM: ACK_SM.FSM.SPARSE
    edn_ack_sm u_edn_ack_sm_ep (
      .clk_i            (clk_i),
      .rst_ni           (rst_ni),
      .enable_i         (edn_enable_fo[AckFsmEn]),
      .req_i            (edn_i[i].edn_req),
      .ack_o            (packer_ep_ack[i]),
      .fifo_not_empty_i (packer_ep_rvalid[i]),
      .fifo_pop_o       (packer_ep_rready[i]),
      .fifo_clr_o       (packer_ep_clr[i]),
      .local_escalate_i (fatal_loc_events),
      .ack_sm_err_o     (edn_ack_sm_err[i])
    );

  end

  // state machine status
  assign hw2reg.main_sm_state.de = 1'b1;
  assign hw2reg.main_sm_state.d = edn_main_sm_state;

  //--------------------------------------------
  // Assertions
  //--------------------------------------------
  // Do not accept new genbits into the CSRNG interface genbits FIFO if we are in the alert state
  // due to a CSRNG status error response.
  `ASSERT(CsErrAcceptNoEntropy_A, reject_csrng_entropy |-> packer_cs_push == 0)
  // Do not issue new commands to the CSRNG if we are in the alert state due to a CSRNG status
  // error response. The only exception is if we need to hold the valid to complete a started
  // handshake.
  `ASSERT(CsErrIssueNoCommands_A, reject_csrng_entropy |->
      csrng_cmd_o.csrng_req_valid == 0 || cs_cmd_req_vld_hold_q == 1'b1)

  //--------------------------------------------
  // unused signals
  //--------------------------------------------

  assign unused_err_code_test_bit = (|err_code_test_bit[19:2]) || (|err_code_test_bit[27:22]);


endmodule
