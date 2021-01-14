// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy distrubution network core module
//  - this module will make requests to the CSRNG module
//    and return the genbits back to up four requesting
//    end points.
//

module edn_core import edn_pkg::*; #(
  parameter int NumEndPoints = 4,
  parameter int BootInsCmd = 32'h0000_0001,
  parameter int BootGenCmd = 32'h0000_1003
) (
  input logic clk_i,
  input logic rst_ni,

  input  edn_reg_pkg::edn_reg2hw_t reg2hw,
  output edn_reg_pkg::edn_hw2reg_t hw2reg,

  // edn interfaces
  input  edn_req_t [NumEndPoints-1:0] edn_i,
  output edn_rsp_t [NumEndPoints-1:0] edn_o,

  // csrng application Interface
  output  csrng_pkg::csrng_req_t  csrng_cmd_o,
  input   csrng_pkg::csrng_rsp_t  csrng_cmd_i,

  output logic        intr_edn_cmd_req_done_o,
  output logic        intr_edn_fifo_err_o
);

  import edn_reg_pkg::*;

//  localparam int EndPointBusWidth = 32;
  localparam int RescmdFifoWidth = 32;
  localparam int RescmdFifoDepth = 13;
  localparam int GencmdFifoWidth = 32;
  localparam int GencmdFifoDepth = 13;
  localparam int CSGenBitsWidth = 128;
  localparam int EndPointBusWidth = 32;

  // signals
  logic event_edn_cmd_req_done;
  logic event_edn_fifo_err;
  logic edn_enable;
  logic cmd_fifo_rst;
  logic packer_arb_valid;
  logic packer_arb_ready;
  logic [NumEndPoints-1:0] packer_arb_req;
  logic [NumEndPoints-1:0] packer_arb_gnt;
  logic                    auto_req_mode;
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
  logic [EndPointBusWidth-1:0] packer_ep_rdata [NumEndPoints];

  // rescmd fifo
  logic [$clog2(RescmdFifoDepth)-1:0] sfifo_rescmd_depth;
  logic [RescmdFifoWidth-1:0]         sfifo_rescmd_rdata;
  logic                               sfifo_rescmd_clr;
  logic                               sfifo_rescmd_push;
  logic [RescmdFifoWidth-1:0]         sfifo_rescmd_wdata;
  logic                               sfifo_rescmd_pop;
  logic [2:0]                         sfifo_rescmd_err;
  logic                               sfifo_rescmd_not_full;
  logic                               sfifo_rescmd_not_empty;

  // gencmd fifo
  logic [GencmdFifoWidth-1:0]         sfifo_gencmd_rdata;
  logic [$clog2(GencmdFifoDepth)-1:0] sfifo_gencmd_depth;
  logic                               sfifo_gencmd_clr;
  logic                               sfifo_gencmd_push;
  logic [GencmdFifoWidth-1:0]         sfifo_gencmd_wdata;
  logic                               sfifo_gencmd_pop;
  logic [2:0]                         sfifo_gencmd_err;
  logic                               sfifo_gencmd_not_full;
  logic                               sfifo_gencmd_not_empty;

  // flops
  logic [31:0]                        cs_cmd_req_q, cs_cmd_req_d;
  logic                               cs_cmd_req_vld_q, cs_cmd_req_vld_d;
  logic [31:0]                        cs_cmd_req_out_q, cs_cmd_req_out_d;
  logic                               cs_cmd_req_vld_out_q, cs_cmd_req_vld_out_d;
  logic [$clog2(RescmdFifoDepth)-1:0] cmd_fifo_cnt_q, cmd_fifo_cnt_d;
  logic                               send_rescmd_q, send_rescmd_d;
  logic                               send_gencmd_q, send_gencmd_d;
  logic [31:0]                        max_reqs_cnt_q, max_reqs_cnt_d;
  logic                               csrng_fips_q, csrng_fips_d;
  logic [NumEndPoints-1:0]            edn_fips_q, edn_fips_d;
  logic [3:0]                         boot_req_q, boot_req_d;
  logic                               boot_auto_req_wack_q, boot_auto_req_wack_d;
  logic                               boot_auto_req_dly_q, boot_auto_req_dly_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      cs_cmd_req_q  <= '0;
      cs_cmd_req_vld_q  <= '0;
      cs_cmd_req_out_q  <= '0;
      cs_cmd_req_vld_out_q  <= '0;
      cmd_fifo_cnt_q <= '0;
      send_rescmd_q <= '0;
      send_gencmd_q <= '0;
      max_reqs_cnt_q <= '0;
      csrng_fips_q <= '0;
      edn_fips_q <= '0;
      boot_req_q <= '0;
      boot_auto_req_wack_q <= '0;
      boot_auto_req_dly_q <= '0;
    end else begin
      cs_cmd_req_q  <= cs_cmd_req_d;
      cs_cmd_req_vld_q  <= cs_cmd_req_vld_d;
      cs_cmd_req_out_q <= cs_cmd_req_out_d;
      cs_cmd_req_vld_out_q <= cs_cmd_req_vld_out_d;
      cmd_fifo_cnt_q <= cmd_fifo_cnt_d;
      send_rescmd_q <= send_rescmd_d;
      send_gencmd_q <= send_gencmd_d;
      max_reqs_cnt_q <= max_reqs_cnt_d;
      csrng_fips_q <= csrng_fips_d;
      edn_fips_q <= edn_fips_d;
      boot_req_q <= boot_req_d;
      boot_auto_req_wack_q <= boot_auto_req_wack_d;
      boot_auto_req_dly_q <= boot_auto_req_dly_d;
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
  ) u_intr_hw_edn_fifo_err (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .event_intr_i           (event_edn_fifo_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.edn_fifo_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.edn_fifo_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.edn_fifo_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.edn_fifo_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.edn_fifo_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.edn_fifo_err.d),
    .intr_o                 (intr_edn_fifo_err_o)
  );

  // interrupt for sw app interface only
  assign event_edn_cmd_req_done = csrng_cmd_ack;

  // set the interrupt sources
  assign event_edn_fifo_err = edn_enable && (
         (|sfifo_rescmd_err) ||
         (|sfifo_gencmd_err));


  // set the err code source bits
  assign hw2reg.err_code.sfifo_rescmd_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_rescmd_err.de = edn_enable && (|sfifo_rescmd_err);

  assign hw2reg.err_code.sfifo_gencmd_err.d = 1'b1;
  assign hw2reg.err_code.sfifo_gencmd_err.de = edn_enable && (|sfifo_gencmd_err);


 // set the err code type bits
  assign hw2reg.err_code.fifo_write_err.d = 1'b1;
  assign hw2reg.err_code.fifo_write_err.de = edn_enable && (
         sfifo_rescmd_err[2] ||
         sfifo_gencmd_err[2]);

  assign hw2reg.err_code.fifo_read_err.d = 1'b1;
  assign hw2reg.err_code.fifo_read_err.de = edn_enable && (
         sfifo_rescmd_err[1] ||
         sfifo_gencmd_err[1]);

  assign hw2reg.err_code.fifo_state_err.d = 1'b1;
  assign hw2reg.err_code.fifo_state_err.de = edn_enable && (
         sfifo_rescmd_err[0] ||
         sfifo_gencmd_err[0]);



  // master module enable
  assign edn_enable = reg2hw.ctrl.edn_enable.q;
  assign cmd_fifo_rst = reg2hw.ctrl.cmd_fifo_rst.q;

  //--------------------------------------------
  // sw register interface
  //--------------------------------------------

  // SW interface connection
  // cmd req
  assign sw_cmd_req_load = reg2hw.sw_cmd_req.qe;
  assign sw_cmd_req_bus = reg2hw.sw_cmd_req.q;
  assign auto_req_mode = reg2hw.ctrl.auto_req_mode.q;
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
         boot_wr_cmd_reg ? BootInsCmd :
         sw_cmd_req_load ? sw_cmd_req_bus :
         cs_cmd_req_q;

  assign cs_cmd_req_vld_d = (sw_cmd_req_load || boot_wr_cmd_reg); // cmd reg write

  assign cs_cmd_req_out_d =
         (!seq_auto_req_mode) ? cs_cmd_req_q :
         send_rescmd ? sfifo_rescmd_rdata :
         send_gencmd ? sfifo_gencmd_rdata :
         cs_cmd_req_out_q;

  assign cs_cmd_req_vld_out_d = seq_auto_req_mode ? (send_rescmd || send_gencmd) :
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
    .wready_o (sfifo_rescmd_not_full),
    .wdata_i  (sfifo_rescmd_wdata),
    .rvalid_o (sfifo_rescmd_not_empty),
    .rready_i (sfifo_rescmd_pop),
    .rdata_o  (sfifo_rescmd_rdata),
    .depth_o  (sfifo_rescmd_depth)
  );

  // feedback cmd back into rescmd fifo
  assign send_rescmd_d = send_rescmd;
  assign sfifo_rescmd_push =
         seq_auto_req_mode ? send_rescmd_q :
         reseed_cmd_load;

  assign sfifo_rescmd_wdata = seq_auto_req_mode ? cs_cmd_req_out_q :  reseed_cmd_bus;

  assign sfifo_rescmd_pop = send_rescmd;

  assign sfifo_rescmd_clr = (cmd_fifo_rst || auto_req_mode_end);

  assign sfifo_rescmd_err =
         {(sfifo_rescmd_push && !sfifo_rescmd_not_full),
          (sfifo_rescmd_pop && !sfifo_rescmd_not_empty),
          (!sfifo_rescmd_not_full && !sfifo_rescmd_not_empty)};

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
    .wready_o (sfifo_gencmd_not_full),
    .wdata_i  (sfifo_gencmd_wdata),
    .rvalid_o (sfifo_gencmd_not_empty),
    .rready_i (sfifo_gencmd_pop),
    .rdata_o  (sfifo_gencmd_rdata),
    .depth_o  (sfifo_gencmd_depth)
  );

  // feedback cmd back into gencmd fifo
  assign send_gencmd_d = send_gencmd;
  assign sfifo_gencmd_push =
         boot_wr_cmd_genfifo ? 1'b1 :
         seq_auto_req_mode ? send_gencmd_q :
         generate_cmd_load;

  assign sfifo_gencmd_wdata =
         boot_wr_cmd_genfifo ? BootGenCmd :
         seq_auto_req_mode ? cs_cmd_req_out_q :
         generate_cmd_bus;

  assign sfifo_gencmd_pop = send_gencmd;

  assign sfifo_gencmd_clr = (cmd_fifo_rst || auto_req_mode_end);

  assign sfifo_gencmd_err =
         {(sfifo_gencmd_push && !sfifo_gencmd_not_full),
          (sfifo_gencmd_pop && !sfifo_gencmd_not_empty),
          (!sfifo_gencmd_not_full && !sfifo_gencmd_not_empty)};

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
    .cmd_sent_i(cmd_sent)
  );


  assign max_reqs_cnt_d =
         (!edn_enable) ? '0 :
         max_reqs_cnt_load ? (max_reqs_between_reseed_bus-1) :
         (send_gencmd && cmd_sent) ? (max_reqs_cnt_q-1) :
         max_reqs_cnt_q;

  assign max_reqs_cnt_load = (max_reqs_between_reseed_load || // sw initial load
                              (send_rescmd && cmd_sent) ||    // runtime decrement
                              auto_req_mode_end);             // restore when auto mode done

  assign max_reqs_cnt_zero = boot_auto_req_dly_q ? 1'b0 : (max_reqs_cnt_q == '0);


  assign cmd_fifo_cnt_d =
         (cmd_fifo_rst || !seq_auto_req_mode) ? '0 :
         capt_gencmd_fifo_cnt ? (sfifo_gencmd_depth-1) :
         capt_rescmd_fifo_cnt ? (sfifo_rescmd_depth-1) :
         (send_gencmd || send_rescmd)? (cmd_fifo_cnt_q-1) :
         cmd_fifo_cnt_q;

  assign cmd_sent = (cmd_fifo_cnt_q == '0);


  // boot request
  assign boot_request = !reg2hw.ctrl.boot_req_dis.q;

  assign boot_req_d[0] =
         (!edn_enable) ? '0 :
         boot_request ? 1'b1 :
         boot_req_q[0];

  assign boot_req_d[3:1] = boot_req_q[2:0];
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
    .req_i(packer_arb_req), // N number of reqs
    .data_i(),
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
     .OutW(CSGenBitsWidth)
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

  assign csrng_fips_d = !edn_enable ? 1'b0 :
         (packer_cs_push && packer_cs_wready) ? csrng_cmd_i.genbits_fips :
         csrng_fips_q;

  //--------------------------------------------
  // end point interface packers generation
  //--------------------------------------------

  for (genvar i = 0; i < NumEndPoints; i=i+1) begin : gen_ep_blk

    prim_packer_fifo #(
      .InW(CSGenBitsWidth),
      .OutW(EndPointBusWidth)
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
      .req_i            (edn_i[i].edn_req),
      .ack_o            (packer_ep_ack[i]),
      .fifo_not_empty_i (packer_ep_rvalid[i]),
      .fifo_pop_o       (packer_ep_rready[i])
    );

  end


  //--------------------------------------------
  // report edn request summary
  //--------------------------------------------

  assign     hw2reg.sum_sts.internal_use.de = !edn_enable;
  assign     hw2reg.sum_sts.internal_use.d  = reg2hw.regen.q;


endmodule
