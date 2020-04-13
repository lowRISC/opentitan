// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng core module
//

module csrng_core import csrng_pkg::*; import entropy_src_pkg::*; #(
  parameter int unsigned NHwApps = 3
) (
  input logic        clk_i,
  input logic        rst_ni,

  input  csrng_reg_pkg::csrng_reg2hw_t reg2hw,
  output csrng_reg_pkg::csrng_hw2reg_t hw2reg,

  // Efuse Interface
  input efuse_sw_app_enable_i,

  // Entropy Interface
  output entropy_src_hw_if_req_t entropy_src_hw_if_o,
  input  entropy_src_hw_if_rsp_t entropy_src_hw_if_i,

  // Application Interfaces
  // instantiation interface
  input  csrng_req_t  [NHwApps:1] csrng_cmd_i,
  output csrng_rsp_t  [NHwApps:1] csrng_cmd_o,

  output logic           cs_cmd_req_done_o,
  output logic           cs_fifo_err_o
);

  import csrng_reg_pkg::*;

//  localparam int unsigned EntrFifoDepth = 16; // real value

  // Bronze gate generator:
  // entr fifo: 16
  // ctr_drbg functions: (24w x 16d) x 5 functions = 1920
  // block_encryption: 768
  // derivation function: 768
  // drbg state save: 512
  localparam int unsigned EntrFifoDepth = 4000;
  localparam int unsigned NApps = NHwApps + 1;
  localparam int unsigned AppCmdWidth = 32;
  localparam int unsigned AppCmdFifoDepth = 16;
  localparam int unsigned GenBitsWidth = 128;

  // signals
  // interrupt signals
  logic       event_cs_cmd_req_done;
  logic       event_cs_fifo_err;
  logic       cs_enable;
  logic       acmd_avail;
  logic [AppCmdWidth-1:0] acmd_bus;
  logic       acmd_accept;
  logic       instant_req;
  logic       reseed_req;
  logic       generate_req;
  logic       update_req;
  logic       uninstant_req;
  logic [3:0] fifo_sel;
  logic       bronze_and_unfinished;
  logic [2:0] acmd;
  logic [3:0] shid;
//  logic [3:0] xcnt;
//  logic [3:0] flgs;
//  logic [15:0] gcnt;

  logic [NApps-1:0] cmd_stage_err;
  logic [NApps-1:0] cmd_stage_vld;
  logic [AppCmdWidth-1:0] cmd_stage_bus[NApps];
  logic [NApps-1:0]       cmd_stage_rdy;
  logic [NApps-1:0]       cmd_arb_req;
  logic [NApps-1:0]       cmd_arb_gnt;
  logic [AppCmdWidth-1:0] cmd_arb_bus[NApps];
  logic [NApps-1:0]       cmd_core_ack;
  logic [3:0]             cmd_core_ack_shid[NApps];
  logic [1:0]             cmd_core_ack_sts[NApps];
  logic [NApps-1:0]       cmd_stage_ack;
  logic [1:0]             cmd_stage_ack_sts[NApps];
  logic [NApps-1:0]       genbits_core_vld;
  logic [NApps-1:0]       genbits_core_rdy;
  logic [GenBitsWidth-1:0] genbits_core_bus[NApps];
  logic [NApps-1:0]       genbits_stage_vld;
  logic [GenBitsWidth-1:0] genbits_stage_bus[NApps];
  logic [NApps-1:0]        genbits_stage_rdy;
  // entropy fifo
  logic [31:0] sfifo_entr_rdata;
  logic [11:0] sfifo_entr_depth; //TOD: use a parameter for size
  logic        sfifo_entr_push;
  logic [31:0] sfifo_entr_wdata;
  logic        sfifo_entr_pop;
  logic        sfifo_entr_err;
  logic        sfifo_entr_not_full;
  logic        sfifo_entr_not_empty;


  prim_intr_hw #(.Width(1)) intr_hw_cs_cmd_req_done (
    .event_intr_i           (event_cs_cmd_req_done),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cs_cmd_req_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cs_cmd_req_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cs_cmd_req_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cs_cmd_req_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cs_cmd_req_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cs_cmd_req_done.d),
    .intr_o                 (cs_cmd_req_done_o)
  );


  prim_intr_hw #(.Width(1)) intr_hw_cs_fifo_err (
    .event_intr_i           (event_cs_fifo_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cs_fifo_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cs_fifo_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cs_fifo_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cs_fifo_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cs_fifo_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cs_fifo_err.d),
    .intr_o                 (cs_fifo_err_o)
  );

  // set the interrupt sources
  assign event_cs_fifo_err =
         (|cmd_stage_err) ||
         sfifo_entr_err; // TODO: add all fifo errors

  // master module enable
  assign cs_enable = reg2hw.cs_ctrl.cs_enable.q;
  // fifo selection for debug
  assign fifo_sel = reg2hw.cs_ctrl.fifo_depth_sts_sel.q;


  //------------------------------------------
  // application interface
  //------------------------------------------

  genvar ai; // app i/f
  generate
    for (ai = 0; ai < NApps; ai = ai+1) begin : gen_app_cmd_if

      csrng_cmd_stage #(.CmdFifoWidth(AppCmdWidth),
                        .CmdFifoDepth(AppCmdFifoDepth))
        u_csrng_cmd_stage
          (
           .clk_i               (clk_i),
           .rst_ni              (rst_ni),
           .cs_enable_i         (cs_enable),
           .cmd_stage_vld_i     (cmd_stage_vld[ai]),
           .cmd_stage_bus_i     (cmd_stage_bus[ai]),
           .cmd_stage_rdy_o     (cmd_stage_rdy[ai]),
           .cmd_arb_req_o       (cmd_arb_req[ai]),
           .cmd_arb_gnt_i       (cmd_arb_gnt[ai]),
           .cmd_arb_bus_o       (cmd_arb_bus[ai]),
           .cmd_ack_i           (cmd_core_ack[ai]),
           .cmd_ack_shid_i      (cmd_core_ack_shid[ai]),
           .cmd_ack_sts_i       (cmd_core_ack_sts[ai]),
           .cmd_stage_ack_o     (cmd_stage_ack[ai]),
           .cmd_stage_ack_sts_o (cmd_stage_ack_sts[ai]),
           .genbits_vld_i       (genbits_core_vld[ai]),
           .genbits_rdy_o       (genbits_core_rdy[ai]),
           .genbits_bus_i       (genbits_core_bus[ai]),
           .genbits_vld_o       (genbits_stage_vld[ai]),
           .genbits_rdy_i       (genbits_stage_rdy[ai]),
           .genbits_bus_o       (genbits_stage_bus[ai]),
           .cmd_stage_err_o     (cmd_stage_err[ai])
           );
    end
  endgenerate

  // SW interface connection (only 1, and must be present)
  // cmd req
  assign cmd_stage_vld[0] = reg2hw.cs_cmd_req.qe;
  assign cmd_stage_bus[0] = reg2hw.cs_cmd_req.q;
  assign hw2reg.cs_cmd_sts.cmd_rdy.de = 1'b1;
  assign hw2reg.cs_cmd_sts.cmd_rdy.d = cmd_stage_rdy[0];
  // cmd ack
  assign hw2reg.cs_cmd_sts.cmd_ack.de = cmd_stage_ack[0];
  assign hw2reg.cs_cmd_sts.cmd_ack.d = 1'b1;
  assign hw2reg.cs_cmd_sts.cmd_sts.de = cmd_stage_ack[0];
  assign hw2reg.cs_cmd_sts.cmd_sts.d = cmd_stage_ack_sts[0];
  // genbits
  assign hw2reg.cs_genbits_vld.d = genbits_stage_vld[0];
  // TODO: size with fifo below
  // TODO: temp mux below for bronze
  assign hw2reg.cs_genbits.d = efuse_sw_app_enable_i ? genbits_stage_bus[0][31:0] :
         sfifo_entr_rdata;
  assign genbits_stage_rdy[0] = 1'b1; //TODO: add packed fifo for sw register size

  // HW interface connections (up to 16, numbered 1-15)
  genvar hai; // hw app i/f
  generate
    for (hai = 1; hai < NApps; hai = hai+1) begin : gen_app_if
      // cmd req
      assign cmd_stage_vld[hai] = csrng_cmd_i[hai].csrng_req_vld;
      assign cmd_stage_bus[hai] = csrng_cmd_i[hai].csrng_req_bus;
      assign csrng_cmd_o[hai].csrng_req_rdy = cmd_stage_rdy[hai];
      // cmd ack
      assign csrng_cmd_o[hai].csrng_rsp_ack = cmd_stage_ack[hai];
      assign csrng_cmd_o[hai].csrng_rsp_sts = cmd_stage_ack_sts[hai];
      // genbits
      assign csrng_cmd_o[hai].genbits_vld = genbits_stage_vld[hai];
      assign csrng_cmd_o[hai].genbits_bus = genbits_stage_bus[hai];
      assign genbits_stage_rdy[hai] = csrng_cmd_i[hai].genbits_rdy;
    end
  endgenerate



  //------------------------------------------
  // app command arbiter and state machine
  //------------------------------------------

  prim_arbiter_ppc #(
                     .N(NApps),  // Number of request ports
                     .DW(AppCmdWidth)) // Data width
    u_prim_arbiter_ppc_acmd
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .req_i(cmd_arb_req),
       .data_i(cmd_arb_bus),
       .gnt_o(cmd_arb_gnt),
       .idx_o(), // NC
       .valid_o(acmd_avail), // 1 req
       .data_o(acmd_bus), // info with req
       .ready_i(acmd_accept) // 1 fsm rdy
       );

  // parse the command bus
  assign acmd = acmd_bus[2:0];
  assign shid = acmd_bus[7:4];
//  assign xcnt = acmd_bus[11:8]; // TODO: connect to flops
//  assign flgs = acmd_bus[15:12];
//  assign gcnt = acmd_bus[31:16];

  // sm to process all instantiation requests
  csrng_main_sm
    u_csrng_main_sm
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .acmd_avail_i(acmd_avail),
       .acmd_accept_o(acmd_accept),
       .acmd_i(acmd),
       .instant_req_o(instant_req),
       .reseed_req_o(reseed_req),
       .generate_req_o(generate_req),
       .update_req_o(update_req),
       .uninstant_req_o(uninstant_req)
       );

  // TODO: use flopped version of shid
  assign event_cs_cmd_req_done = (instant_req ||
                                  reseed_req ||
                                  generate_req ||
                                  update_req ||
                                  uninstant_req) && (shid == 4'h0);


  // TODO: remove patches
  genvar csi; // command stage i/f
  generate
    for (csi = 0; csi < NApps; csi = csi+1) begin : gen_cmd_if
      assign cmd_core_ack[csi] = 1'b0;
      assign cmd_core_ack_shid[csi] = '0;
      assign cmd_core_ack_sts[csi] = '0;
      assign genbits_core_vld[csi] = '0;
      assign genbits_core_bus[csi] = '0;
    end
  endgenerate


  //--------------------------------------------
  // entropy fifo
  //--------------------------------------------


      prim_fifo_sync # (.Width(32),.Pass(0),.Depth(EntrFifoDepth))
        u_prim_fifo_sync_entr
          (
           .clk_i          (clk_i),
           .rst_ni         (rst_ni),
           .clr_i          (!cs_enable),
           .wvalid         (sfifo_entr_push),
           .wready         (sfifo_entr_not_full),
           .wdata          (sfifo_entr_wdata),
           .rvalid         (sfifo_entr_not_empty),
           .rready         (sfifo_entr_pop),
           .rdata          (sfifo_entr_rdata),
           .depth          (sfifo_entr_depth)
           );

  assign entropy_src_hw_if_o.entropy_src_rdy = cs_enable && sfifo_entr_not_full;

  assign sfifo_entr_wdata = entropy_src_hw_if_i.entropy_src_bits;

  // TODO: log elsewhere? see logic below
  assign sfifo_entr_push = cs_enable & entropy_src_hw_if_i.entropy_src_vld;
  assign sfifo_entr_pop = 1'b0; // TODO: Set by main sm

  // fifo err
  assign sfifo_entr_err =
         (sfifo_entr_push && !sfifo_entr_not_full) ||
         (sfifo_entr_pop && !sfifo_entr_not_empty);



  //--------------------------------------------
  // report csrng request summary
  //--------------------------------------------

  assign     hw2reg.cs_sum_sts.fifo_depth_sts.de = cs_enable;
  assign     hw2reg.cs_sum_sts.fifo_depth_sts.d  =
             (fifo_sel == 4'h0) ? {13'b0,sfifo_entr_depth} : // TODO: use param
             (fifo_sel == 4'h1) ? {16'b0,sfifo_entr_rdata[15:0]} : // TODO: unfinished
             (fifo_sel == 4'h2) ? {16'b0,sfifo_entr_rdata[31:16]} : // TODO: unfinished
             24'b0;


  assign     hw2reg.cs_sum_sts.diag.de = ~cs_enable;
  assign     hw2reg.cs_sum_sts.diag.d  =
             bronze_and_unfinished;


  assign     bronze_and_unfinished =  // TODO: eventually use these
                                      (reg2hw.cs_regen)          || // not used
                                      (|reg2hw.cs_genbits.q)     || // not used
                                      (reg2hw.cs_genbits.re)     || // not used
                                      (efuse_sw_app_enable_i   ) || // TODO: unfinished
                                      (|acmd_bus)                || // TODO: unfinished
                                      (|genbits_stage_bus[0])    || // TODO: unfinished
                                      (|genbits_core_rdy);          // TODO: unfinished





endmodule
