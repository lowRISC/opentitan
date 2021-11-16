// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy distrubution network core module
//  - this module will make requests to the CSRNG module
//    and return the genbits back to up four requesting
//    end points.
//

module edn_core import edn_pkg::*;
#(
  parameter int NumEndPoints = 4,
  parameter int BootInsCmd = 32'h0000_0001,
  parameter int BootGenCmd = 32'h0000_1003
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

  // signals
  logic event_edn_cmd_req_done;
  logic event_edn_fatal_err;
  logic edn_enable;
  logic edn_enable_pfe;
  logic edn_enable_pfa;
  logic cmd_fifo_rst;
  logic cmd_fifo_rst_pfe;
  logic cmd_fifo_rst_pfa;
  logic packer_arb_valid;
  logic packer_arb_ready;
  logic [NumEndPoints-1:0] packer_arb_req;
  logic [NumEndPoints-1:0] packer_arb_gnt;
  logic                    auto_req_mode;
  logic                    auto_req_mode_pfe;
  logic                    auto_req_mode_pfa;
  logic                    seq_auto_req_mode;
  logic                    auto_req_mode_end;
  logic                    capt_gencmd_fifo_cnt;
  logic                    capt_rescmd_fifo_cnt;
  logic                    max_reqs_cnt_zero;
  logic                    max_reqs_cnt_load;
  logic                    max_reqs_between_reseed_load;
  logic [31:0]             max_reqs_between_reseed_bus;
  logic                    csrng_cmd_ack;
  logic                    send_rescmd;
  logic                    cmd_sent;
  logic                    send_gencmd;
  logic                    sw_cmd_req_load;
  logic [31:0]             sw_cmd_req_bus;
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
  logic                      boot_request;
  logic                      boot_req_mode_pfe;
  logic                      boot_req_mode_pfa;
  logic                      boot_wr_cmd_reg;
  logic                      boot_wr_cmd_genfifo;
  logic                      boot_auto_req;

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

  logic                               edn_main_sm_err_sum;
  logic                               edn_main_sm_err;
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

  // unused
  logic                               unused_err_code_test_bit;

  // flops
  logic [31:0]                        cs_cmd_req_q, cs_cmd_req_d;
  logic                               cs_cmd_req_vld_q, cs_cmd_req_vld_d;
  logic [31:0]                        cs_cmd_req_out_q, cs_cmd_req_out_d;
  logic                               cs_cmd_req_vld_out_q, cs_cmd_req_vld_out_d;
  logic [RescmdFifoIdxWidth-1:0]      cmd_fifo_cnt_q, cmd_fifo_cnt_d;
  logic                               send_rescmd_q, send_rescmd_d;
  logic                               send_gencmd_q, send_gencmd_d;
  logic                               csrng_fips_q, csrng_fips_d;
  logic [NumEndPoints-1:0]            edn_fips_q, edn_fips_d;
  logic [3:0]                         boot_req_q, boot_req_d;
  logic                               boot_auto_req_wack_q, boot_auto_req_wack_d;
  logic                               boot_auto_req_dly_q, boot_auto_req_dly_d;
  logic [63:0]                        cs_rdata_capt_q, cs_rdata_capt_d;
  logic                               cs_rdata_capt_vld_q, cs_rdata_capt_vld_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      cs_cmd_req_q  <= '0;
      cs_cmd_req_vld_q  <= '0;
      cs_cmd_req_out_q  <= '0;
      cs_cmd_req_vld_out_q  <= '0;
      cmd_fifo_cnt_q <= '0;
      send_rescmd_q <= '0;
      send_gencmd_q <= '0;
      csrng_fips_q <= '0;
      edn_fips_q <= '0;
      boot_req_q <= '0;
      boot_auto_req_wack_q <= '0;
      boot_auto_req_dly_q <= '0;
      cs_rdata_capt_q <= '0;
      cs_rdata_capt_vld_q <= '0;
    end else begin
      cs_cmd_req_q  <= cs_cmd_req_d;
      cs_cmd_req_vld_q  <= cs_cmd_req_vld_d;
      cs_cmd_req_out_q <= cs_cmd_req_out_d;
      cs_cmd_req_vld_out_q <= cs_cmd_req_vld_out_d;
      cmd_fifo_cnt_q <= cmd_fifo_cnt_d;
      send_rescmd_q <= send_rescmd_d;
      send_gencmd_q <= send_gencmd_d;
      csrng_fips_q <= csrng_fips_d;
      edn_fips_q <= edn_fips_d;
      boot_req_q <= boot_req_d;
      boot_auto_req_wack_q <= boot_auto_req_wack_d;
      boot_auto_req_dly_q <= boot_auto_req_dly_d;
      cs_rdata_capt_q <= cs_rdata_capt_d;
      cs_rdata_capt_vld_q <= cs_rdata_capt_vld_d;
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
  assign event_edn_cmd_req_done = csrng_cmd_ack;

  // set the interrupt sources
  assign event_edn_fatal_err = (edn_enable && (
         sfifo_rescmd_err_sum ||
         sfifo_gencmd_err_sum ||
         edn_ack_sm_err_sum ||
         edn_main_sm_err_sum)) ||
         edn_cntr_err_sum;

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
  assign hw2reg.err_code.sfifo_rescmd_err.de = edn_enable && sfifo_rescmd_err_sum;

  assign hw2reg.err_code.sfifo_gencmd_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_gencmd_err.de = edn_enable && sfifo_gencmd_err_sum;

  assign hw2reg.err_code.edn_ack_sm_err.d = 1'b1;
  assign hw2reg.err_code.edn_ack_sm_err.de = edn_enable && edn_ack_sm_err_sum;

  assign hw2reg.err_code.edn_main_sm_err.d = 1'b1;
  assign hw2reg.err_code.edn_main_sm_err.de = edn_enable && edn_main_sm_err_sum;

  assign hw2reg.err_code.edn_cntr_err.d = 1'b1;
  assign hw2reg.err_code.edn_cntr_err.de = edn_cntr_err_sum;


 // set the err code type bits
  assign hw2reg.err_code.fifo_write_err.d = 1'b1;
  assign hw2reg.err_code.fifo_write_err.de = edn_enable && fifo_write_err_sum;

  assign hw2reg.err_code.fifo_read_err.d = 1'b1;
  assign hw2reg.err_code.fifo_read_err.de = edn_enable && fifo_read_err_sum;

  assign hw2reg.err_code.fifo_state_err.d = 1'b1;
  assign hw2reg.err_code.fifo_state_err.de = edn_enable && fifo_status_err_sum;


  // Error forcing
  for (genvar i = 0; i < 31; i = i+1) begin : gen_err_code_test_bit
    assign err_code_test_bit[i] = (reg2hw.err_code_test.q == i) && reg2hw.err_code_test.qe;
  end : gen_err_code_test_bit


  // alert - send all interrupt sources to the alert for the fatal case
  assign fatal_alert_o = event_edn_fatal_err;

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
  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_test_invalid;

  mubi4_t mubi_edn_enable;
  assign mubi_edn_enable = mubi4_t'(reg2hw.ctrl.edn_enable.q);
  assign edn_enable_pfe = mubi4_test_true_strict(mubi_edn_enable);
  assign edn_enable_pfa = mubi4_test_invalid(mubi_edn_enable);
  assign hw2reg.recov_alert_sts.edn_enable_field_alert.de = edn_enable_pfa;
  assign hw2reg.recov_alert_sts.edn_enable_field_alert.d  = edn_enable_pfa;

  mubi4_t mubi_cmd_fifo_rst;
  assign mubi_cmd_fifo_rst = mubi4_t'(reg2hw.ctrl.cmd_fifo_rst.q);
  assign cmd_fifo_rst_pfe = mubi4_test_true_strict(mubi_cmd_fifo_rst);
  assign cmd_fifo_rst_pfa = mubi4_test_invalid(mubi_cmd_fifo_rst);
  assign hw2reg.recov_alert_sts.cmd_fifo_rst_field_alert.de = cmd_fifo_rst_pfa;
  assign hw2reg.recov_alert_sts.cmd_fifo_rst_field_alert.d  = cmd_fifo_rst_pfa;

  // counter errors
  assign edn_cntr_err = max_reqs_cnt_err;

  // master module enable
  assign edn_enable = edn_enable_pfe;
  assign cmd_fifo_rst = cmd_fifo_rst_pfe;

  //--------------------------------------------
  // sw register interface
  //--------------------------------------------
  mubi4_t mubi_auto_req_mode;
  assign mubi_auto_req_mode = mubi4_t'(reg2hw.ctrl.auto_req_mode.q);
  assign auto_req_mode_pfe = mubi4_test_true_strict(mubi_auto_req_mode);
  assign auto_req_mode_pfa = mubi4_test_invalid(mubi_auto_req_mode);
  assign hw2reg.recov_alert_sts.auto_req_mode_field_alert.de = auto_req_mode_pfa;
  assign hw2reg.recov_alert_sts.auto_req_mode_field_alert.d  = auto_req_mode_pfa;


  // SW interface connection
  // cmd req
  assign auto_req_mode = auto_req_mode_pfe;
  assign sw_cmd_req_load = reg2hw.sw_cmd_req.qe;
  assign sw_cmd_req_bus = reg2hw.sw_cmd_req.q;
  assign hw2reg.sum_sts.req_mode_sm_sts.de = 1'b1;
  assign hw2reg.sum_sts.req_mode_sm_sts.d = seq_auto_req_mode;
  assign hw2reg.sum_sts.boot_inst_ack.de = 1'b1;
  assign hw2reg.sum_sts.boot_inst_ack.d = csrng_cmd_ack && boot_request;

  assign max_reqs_between_reseed_load = reg2hw.max_num_reqs_between_reseeds.qe;
  assign max_reqs_between_reseed_bus = reg2hw.max_num_reqs_between_reseeds.q;

  assign reseed_cmd_load = reg2hw.reseed_cmd.qe;
  assign reseed_cmd_bus = reg2hw.reseed_cmd.q;

  assign generate_cmd_load = reg2hw.generate_cmd.qe;
  assign generate_cmd_bus = reg2hw.generate_cmd.q;

  assign cs_cmd_req_d =
         (!edn_enable) ? '0 :
         boot_wr_cmd_reg ? BootInsCmd :
         sw_cmd_req_load ? sw_cmd_req_bus :
         cs_cmd_req_q;

  assign cs_cmd_req_vld_d =
         (!edn_enable) ? '0 :
         (sw_cmd_req_load || boot_wr_cmd_reg); // cmd reg write

  assign cs_cmd_req_out_d =
         (!edn_enable) ? '0 :
         (!seq_auto_req_mode) ? cs_cmd_req_q :
         send_rescmd ? sfifo_rescmd_rdata :
         send_gencmd ? sfifo_gencmd_rdata :
         cs_cmd_req_out_q;

  assign cs_cmd_req_vld_out_d =
         (!edn_enable) ? '0 :
         seq_auto_req_mode ? (send_rescmd || send_gencmd) :
         cs_cmd_req_vld_q;

  // drive outputs
  assign csrng_cmd_o.csrng_req_valid = cs_cmd_req_vld_out_q;
  assign csrng_cmd_o.csrng_req_bus = cs_cmd_req_out_q;

  // receive rdy
  assign hw2reg.sw_cmd_sts.cmd_rdy.de = 1'b1;
  assign hw2reg.sw_cmd_sts.cmd_rdy.d = csrng_cmd_i.csrng_req_ready;
  // receive cmd ack
  assign csrng_cmd_ack = csrng_cmd_i.csrng_rsp_ack;
  assign hw2reg.sw_cmd_sts.cmd_sts.de = csrng_cmd_ack;
  assign hw2reg.sw_cmd_sts.cmd_sts.d = csrng_cmd_i.csrng_rsp_sts;

  // rescmd fifo
  prim_fifo_sync #(
    .Width(RescmdFifoWidth),
    .Pass(0),
    .Depth(RescmdFifoDepth)
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
    .depth_o  (sfifo_rescmd_depth)
  );

  // feedback cmd back into rescmd fifo
  assign send_rescmd_d =
         (!edn_enable) ? '0 :
         send_rescmd;

  assign sfifo_rescmd_push =
         seq_auto_req_mode ? send_rescmd_q :
         reseed_cmd_load;

  assign sfifo_rescmd_wdata = seq_auto_req_mode ? cs_cmd_req_out_q :  reseed_cmd_bus;

  assign sfifo_rescmd_pop = send_rescmd;

  assign sfifo_rescmd_clr =
         (!edn_enable) ? '0 :
         (cmd_fifo_rst || auto_req_mode_end);

  assign sfifo_rescmd_err =
         {(sfifo_rescmd_push && sfifo_rescmd_full),
          (sfifo_rescmd_pop && !sfifo_rescmd_not_empty),
          (sfifo_rescmd_full && !sfifo_rescmd_not_empty)};

  // gencmd fifo
  prim_fifo_sync #(
    .Width(GencmdFifoWidth),
    .Pass(0),
    .Depth(GencmdFifoDepth)
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
    .depth_o  (sfifo_gencmd_depth)
  );

  // feedback cmd back into gencmd fifo
  assign send_gencmd_d =
         (!edn_enable) ? '0 :
         send_gencmd;

  assign sfifo_gencmd_push =
         (!edn_enable) ? '0 :
         boot_wr_cmd_genfifo ? 1'b1 :
         seq_auto_req_mode ? send_gencmd_q :
         generate_cmd_load;

  assign sfifo_gencmd_wdata =
         (!edn_enable) ? '0 :
         boot_wr_cmd_genfifo ? BootGenCmd :
         seq_auto_req_mode ? cs_cmd_req_out_q :
         generate_cmd_bus;

  assign sfifo_gencmd_pop = send_gencmd;

  assign sfifo_gencmd_clr =
         (!edn_enable) ? '0 :
         (cmd_fifo_rst || auto_req_mode_end);

  assign sfifo_gencmd_err =
         {(sfifo_gencmd_push && sfifo_gencmd_full),
          (sfifo_gencmd_pop && !sfifo_gencmd_not_empty),
          (sfifo_gencmd_full && !sfifo_gencmd_not_empty)};

  // sm to process csrng commands
  edn_main_sm u_edn_main_sm (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .auto_req_mode_i(auto_req_mode || boot_auto_req_dly_q),
    .seq_auto_req_mode_o(seq_auto_req_mode),
    .auto_req_mode_end_o(auto_req_mode_end),
    .csrng_cmd_ack_i(csrng_cmd_ack),
    .capt_gencmd_fifo_cnt_o(capt_gencmd_fifo_cnt),
    .send_gencmd_o(send_gencmd),
    .max_reqs_cnt_zero_i(max_reqs_cnt_zero),
    .capt_rescmd_fifo_cnt_o(capt_rescmd_fifo_cnt),
    .send_rescmd_o(send_rescmd),
    .cmd_sent_i(cmd_sent),
    .main_sm_err_o(edn_main_sm_err)
  );


  // Maximum requests counter for a generate command
    prim_count #(
        .Width(RegWidth),
        .OutSelDnCnt(1'b1), // count down
        .CntStyle(prim_count_pkg::CrossCnt)
      ) u_prim_count_max_reqs_cntr (
        .clk_i,
        .rst_ni,
        .clr_i(1'b0),
        .set_i(max_reqs_cnt_load),
        .set_cnt_i(max_reqs_between_reseed_bus-1),
        .en_i(send_gencmd && cmd_sent),
        .step_i(RegWidth'(1)),
        .cnt_o(max_reqs_cnt),
        .err_o(max_reqs_cnt_err)
      );

  assign max_reqs_cnt_load = (max_reqs_between_reseed_load || // sw initial load
                              (send_rescmd && cmd_sent) ||    // runtime decrement
                              auto_req_mode_end);             // restore when auto mode done

  assign max_reqs_cnt_zero = boot_auto_req_dly_q ? 1'b0 : (max_reqs_cnt == '0);


  assign cmd_fifo_cnt_d =
         (!edn_enable) ? '0 :
         (cmd_fifo_rst || !seq_auto_req_mode) ? '0 :
         capt_gencmd_fifo_cnt ? (sfifo_gencmd_depth) :
         capt_rescmd_fifo_cnt ? (sfifo_rescmd_depth) :
         (send_gencmd || send_rescmd)? (cmd_fifo_cnt_q-1) :
         cmd_fifo_cnt_q;

  assign cmd_sent = (cmd_fifo_cnt_q == RescmdFifoIdxWidth'(1));

  mubi4_t mubi_boot_req_mode;
  assign mubi_boot_req_mode = mubi4_t'(reg2hw.ctrl.boot_req_mode.q);
  assign boot_req_mode_pfe = mubi4_test_true_strict(mubi_boot_req_mode);
  assign boot_req_mode_pfa = mubi4_test_invalid(mubi_boot_req_mode);
  assign hw2reg.recov_alert_sts.boot_req_mode_field_alert.de = boot_req_mode_pfa;
  assign hw2reg.recov_alert_sts.boot_req_mode_field_alert.d  = boot_req_mode_pfa;


  // boot request
  assign boot_request = boot_req_mode_pfe;

  assign boot_req_d[0] =
         (!edn_enable) ? '0 :
         boot_request ? 1'b1 :
         boot_req_q[0];

  assign boot_req_d[3:1] =
         (!edn_enable) ? '0 :
         boot_req_q[2:0];

  assign boot_wr_cmd_reg = !boot_req_q[1] && boot_req_q[0];
  assign boot_wr_cmd_genfifo =!boot_req_q[2] && boot_req_q[1];
  assign boot_auto_req = !boot_req_q[3] && boot_req_q[2];

  assign boot_auto_req_wack_d =
         (!edn_enable) ? '0 :
         boot_auto_req ? 1'b1 :
         csrng_cmd_ack ? 1'b0 :
         boot_auto_req_wack_q;

  assign boot_auto_req_dly_d =
         (!edn_enable) ? '0 :
         boot_auto_req_wack_q;


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

  assign packer_cs_clr = !edn_enable;
  assign packer_cs_push = csrng_cmd_i.genbits_valid;
  assign packer_cs_wdata = csrng_cmd_i.genbits_bus;
  assign csrng_cmd_o.genbits_ready = packer_cs_wready;
  assign packer_cs_rready = packer_arb_valid;
  assign packer_arb_ready = packer_cs_rvalid;

  assign csrng_fips_d =
         !edn_enable ? 1'b0 :
         (packer_cs_push && packer_cs_wready) ? csrng_cmd_i.genbits_fips :
         csrng_fips_q;

  //--------------------------------------------
  // data path integrity check
  // - a counter meansure to entropy bus tampering
  // - checks to make sure repeated data sets off
  //   an alert for sw to handle
  //--------------------------------------------

  // capture a copy of the entropy data
  assign cs_rdata_capt_vld = (packer_cs_rvalid && packer_cs_rready);

  assign cs_rdata_capt_d = cs_rdata_capt_vld ? packer_cs_rdata[63:0] : cs_rdata_capt_q;

  assign cs_rdata_capt_vld_d =
         !edn_enable ? 1'b0 :
         cs_rdata_capt_vld ? 1'b1 :
         cs_rdata_capt_vld_q;

  // continuous compare of the entropy data
  assign edn_bus_cmp_alert = cs_rdata_capt_vld && cs_rdata_capt_vld_q &&
         (cs_rdata_capt_q == packer_cs_rdata[63:0]);

  assign recov_alert_o = edn_bus_cmp_alert;

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

    assign packer_ep_clr[i] = !edn_enable;
    assign packer_ep_push[i] = packer_arb_valid && packer_ep_wready[i] && packer_arb_gnt[i];
    assign packer_ep_wdata[i] = packer_cs_rdata;

    // fips indication
    assign edn_fips_d[i] = !edn_enable ? 1'b0 :
           (packer_ep_push[i] && packer_ep_wready[i]) ?  csrng_fips_q :
           edn_fips_q[i];
    assign edn_o[i].edn_fips = edn_fips_q[i];

    // gate returned data
    assign edn_o[i].edn_ack = packer_ep_ack[i];
    assign edn_o[i].edn_bus = packer_ep_rdata[i];

    edn_ack_sm u_edn_ack_sm_ep (
      .clk_i            (clk_i),
      .rst_ni           (rst_ni),
      .enable_i         (edn_enable),
      .req_i            (edn_i[i].edn_req),
      .ack_o            (packer_ep_ack[i]),
      .fifo_not_empty_i (packer_ep_rvalid[i]),
      .fifo_pop_o       (packer_ep_rready[i]),
      .ack_sm_err_o     (edn_ack_sm_err[i])
    );

  end


  //--------------------------------------------
  // unused signals
  //--------------------------------------------

  assign unused_err_code_test_bit = (|err_code_test_bit[19:2]) || (|err_code_test_bit[27:22]);


endmodule
