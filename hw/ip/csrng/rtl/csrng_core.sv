// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng core module
//

module csrng_core import csrng_pkg::*; #(
  parameter int unsigned NHwApps = 3
) (
  input logic        clk_i,
  input logic        rst_ni,

  input  csrng_reg_pkg::csrng_reg2hw_t reg2hw,
  output csrng_reg_pkg::csrng_hw2reg_t hw2reg,

  // Efuse Interface
  input efuse_sw_app_enable_i,

  // Entropy Interface
  output entropy_src_pkg::entropy_src_hw_if_req_t entropy_src_hw_if_o,
  input  entropy_src_pkg::entropy_src_hw_if_rsp_t entropy_src_hw_if_i,

  // Application Interfaces
  // instantiation interface
  input  csrng_req_t  [NHwApps-1:0] csrng_cmd_i,
  output csrng_rsp_t  [NHwApps-1:0] csrng_cmd_o,

  output logic           intr_cs_cmd_req_done_o,
  output logic           intr_cs_fifo_err_o
);

  import csrng_reg_pkg::*;

  localparam int unsigned EntrFifoDepth = 16;
  localparam int unsigned PEntrFifoDepth = 2;
  localparam int unsigned NApps = NHwApps + 1;
  localparam int unsigned AppCmdWidth = 32;
  localparam int unsigned AppCmdFifoDepth = 13;
  localparam int unsigned GenBitsWidth = 128;
  localparam int unsigned Cmd = 3;
  localparam int unsigned StateId = 4;
  localparam int unsigned KeyLen = 256;
  localparam int unsigned BlkLen = 128;
  localparam int unsigned SeedLen = 384;
  localparam int unsigned CtrLen = 32;
  localparam int unsigned NumBlkEncReqs = 2;
  localparam int unsigned BlkEncArbWidth = KeyLen+BlkLen+StateId+Cmd;
  localparam int unsigned NumUpdateReqs = 2;
  localparam int unsigned UpdateArbWidth = KeyLen+BlkLen+SeedLen+StateId+Cmd;

  typedef enum logic [2:0] {
                            INS = 3'h0,
                            RES = 3'h1,
                            GEN = 3'h2,
                            UPD = 3'h3,
                            UNI = 3'h4
                            } acmd_e;

  // signals
  // interrupt signals
  logic       event_cs_cmd_req_done;
  logic       event_cs_fifo_err;
  logic       cs_enable;
  logic       aes_cipher_enable;
  logic       acmd_avail;
  logic       acmd_sop;
  logic       acmd_mop;
  logic       acmd_eop;

  logic       cmd_blk_select;
  logic       gen_blk_select;
  logic       state_db_wr_req_rdy;
  logic       state_db_wr_req;
  logic [StateId-1:0] state_db_wr_inst_id;
  logic [KeyLen-1:0]  state_db_wr_key;
  logic [BlkLen-1:0]  state_db_wr_v;
  logic [CtrLen-1:0]  state_db_wr_rc;
  logic [1:0]         state_db_wr_sts_code;

  logic [AppCmdWidth-1:0] acmd_bus;
  logic [SeedLen-1:0]     packer_adata;
  logic                   packer_entropy_vld;
  logic                   cmd_entropy_avail;
  logic [SeedLen-1:0]     cmd_entropy;

  logic                   cmd_result_wr_req;
  logic                   cmd_result_ack;
  logic [1:0]             cmd_result_ack_sts;
  logic [Cmd-1:0]         cmd_result_ccmd;
  logic                   cmd_result_ack_rdy;
  logic [StateId-1:0]     cmd_result_inst_id;
  logic [KeyLen-1:0]      cmd_result_key;
  logic [BlkLen-1:0]      cmd_result_v;
  logic [CtrLen-1:0]      cmd_result_rc;
  logic [15:0]            cmd_result_gcnt;
  logic                   state_db_sts_ack;
  logic [1:0]             state_db_sts_code;
  logic [StateId-1:0]     state_db_sts_id;
  logic                   state_db_fifo_err;

  logic                   gen_result_wr_req;
  logic [1:0]             gen_result_ack_sts;
  logic                   gen_result_ack_rdy;
  logic [StateId-1:0]     gen_result_inst_id;
  logic [KeyLen-1:0]      gen_result_key;
  logic [BlkLen-1:0]      gen_result_v;
  logic [CtrLen-1:0]      gen_result_rc;
  logic [BlkLen-1:0]      gen_result_bits;

  logic                   acmd_accept;
  logic                   instant_req;
  logic                   reseed_req;
  logic                   generate_req;
  logic                   update_req;
  logic                   uninstant_req;
  logic [3:0]             fifo_sel;
  logic                   state_db_rd_req;
  logic                   ctr_drbg_cmd_req;
  logic                   ctr_drbg_gen_req;
  logic                   ctr_drbg_cmd_req_rdy;
  logic                   ctr_drbg_cmd_fifo_err;
  logic                   ctr_drbg_upd_fifo_err;
  logic                   ctr_drbg_gen_fifo_err;
  logic                   block_encrypt_fifo_err;
  logic [KeyLen-1:0]      state_db_rd_key;
  logic [BlkLen-1:0]      state_db_rd_v;
  logic [CtrLen-1:0]      state_db_rd_rc;
  logic [2:0]             acmd;
  logic [3:0]             shid;
  logic                   flag0;
  logic [15:0]            gcnt;

  // blk encrypt arbiter
  logic [Cmd-1:0]         updblk_benblk_cmd_arb_din;
  logic [StateId-1:0]     updblk_benblk_id_arb_din;
  logic [BlkLen-1:0]      updblk_benblk_v_arb_din;
  logic [KeyLen-1:0]      updblk_benblk_key_arb_din;
  logic                   updblk_benblk_arb_req;
  logic                   updblk_benblk_arb_req_rdy;
  logic                   benblk_updblk_ack;
  logic                   updblk_benblk_ack_rdy;

  logic [Cmd-1:0]         genblk_benblk_cmd_arb_din;
  logic [StateId-1:0]     genblk_benblk_id_arb_din;
  logic [BlkLen-1:0]      genblk_benblk_v_arb_din;
  logic [KeyLen-1:0]      genblk_benblk_key_arb_din;
  logic                   genblk_benblk_arb_req;
  logic                   genblk_benblk_arb_req_rdy;
  logic                   benblk_genblk_ack;
  logic                   genblk_benblk_ack_rdy;

  logic [BlkEncArbWidth-1:0] benblk_arb_din [2];
  logic [BlkEncArbWidth-1:0] benblk_arb_data;
  logic [KeyLen-1:0]         benblk_arb_key;
  logic [BlkLen-1:0]         benblk_arb_v;
  logic [StateId-1:0]        benblk_arb_inst_id;
  logic [Cmd-1:0]            benblk_arb_cmd;
  logic                      benblk_arb_vld;
  logic                      benblk_ack;
  logic                      benblk_ack_rdy;
  logic                      benblk_arb_rdy;
  logic [Cmd-1:0]            benblk_cmd;
  logic [StateId-1:0]        benblk_inst_id;
  logic [BlkLen-1:0]         benblk_v;

  // update arbiter
  logic [Cmd-1:0]            cmdblk_updblk_ccmd_arb_din;
  logic [StateId-1:0]        cmdblk_updblk_id_arb_din;
  logic [BlkLen-1:0]         cmdblk_updblk_v_arb_din;
  logic [KeyLen-1:0]         cmdblk_updblk_key_arb_din;
  logic [SeedLen-1:0]        cmdblk_updblk_pdata_arb_din;
  logic                      cmdblk_updblk_arb_req;
  logic                      updblk_cmdblk_arb_req_rdy;
  logic                      updblk_cmdblk_ack;
  logic                      cmdblk_updblk_ack_rdy;

  logic [Cmd-1:0]            genblk_updblk_ccmd_arb_din;
  logic [StateId-1:0]        genblk_updblk_id_arb_din;
  logic [BlkLen-1:0]         genblk_updblk_v_arb_din;
  logic [KeyLen-1:0]         genblk_updblk_key_arb_din;
  logic [SeedLen-1:0]        genblk_updblk_pdata_arb_din;
  logic                      genblk_updblk_arb_req;
  logic                      updblk_genblk_arb_req_rdy;
  logic                      updblk_genblk_ack;
  logic                      genblk_updblk_ack_rdy;

  logic [UpdateArbWidth-1:0] updblk_arb_din [2];
  logic [UpdateArbWidth-1:0] updblk_arb_data;
  logic [KeyLen-1:0]         updblk_arb_key;
  logic [BlkLen-1:0]         updblk_arb_v;
  logic [SeedLen-1:0]        updblk_arb_pdata;
  logic [StateId-1:0]        updblk_arb_inst_id;
  logic [Cmd-1:0]            updblk_arb_ccmd;
  logic                      updblk_arb_vld;
  logic                      updblk_ack;
  logic                      updblk_ack_rdy;
  logic                      updblk_arb_rdy;
  logic [Cmd-1:0]            updblk_ccmd;
  logic [StateId-1:0]        updblk_inst_id;
  logic [KeyLen-1:0]         updblk_key;
  logic [BlkLen-1:0]         updblk_v;

  logic [NApps-1:0]          cmd_stage_err;
  logic [NApps-1:0] cmd_stage_vld;
  logic [AppCmdWidth-1:0] cmd_stage_bus[NApps];
  logic [NApps-1:0]       cmd_stage_rdy;
  logic [NApps-1:0]       cmd_arb_req;
  logic [NApps-1:0]       cmd_arb_gnt;
  logic [NApps-1:0]       cmd_arb_sop;
  logic [NApps-1:0]       cmd_arb_mop;
  logic [NApps-1:0]       cmd_arb_eop;
  logic [AppCmdWidth-1:0] cmd_arb_bus[NApps];
  logic [NApps-1:0]       cmd_core_ack;
  logic [1:0]             cmd_core_ack_sts[NApps];
  logic [NApps-1:0]       cmd_stage_ack;
  logic [1:0]             cmd_stage_ack_sts[NApps];
  logic [NApps-1:0]       genbits_core_vld;
  logic [NApps-1:0]       genbits_core_rdy;
  logic [GenBitsWidth-1:0] genbits_core_bus[NApps];
  logic [NApps-1:0]        genbits_stage_vld;
  logic [GenBitsWidth-1:0] genbits_stage_bus[NApps];
  logic [NApps-1:0]        genbits_stage_rdy;
  logic                    genbits_stage_vld_sw;
  logic [31:0]             genbits_stage_bus_sw;

  // entropy fifo
  logic [31:0]             sfifo_entr_rdata;
  logic [$clog2(EntrFifoDepth):0]  sfifo_entr_depth;
  logic                            sfifo_entr_push;
  logic [31:0]                     sfifo_entr_wdata;
  logic                            sfifo_entr_pop;
  logic                            sfifo_entr_err;
  logic                            sfifo_entr_not_full;
  logic                            sfifo_entr_not_empty;
// packed entropy fifo
  logic [SeedLen-1:0] sfifo_pentr_rdata;
  logic [$clog2(PEntrFifoDepth):0] sfifo_pentr_depth;
  logic               sfifo_pentr_push;
  logic [SeedLen-1:0] sfifo_pentr_wdata;
  logic               sfifo_pentr_pop;
  logic               sfifo_pentr_err;
  logic               sfifo_pentr_not_full;
  logic               sfifo_pentr_not_empty;
  logic               sfifo_pentr_avail;

  // flops
  logic [2:0]  acmd_q, acmd_d;
  logic [3:0]  shid_q, shid_d;
  logic        flag0_q, flag0_d;
  logic [15:0] gcnt_q, gcnt_d;
  logic        statedb_wr_select_q, statedb_wr_select_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      acmd_q  <= '0;
      shid_q  <= '0;
      flag0_q <= '0;
      gcnt_q <= '0;
      statedb_wr_select_q <= '0;
    end else begin
      acmd_q  <= acmd_d;
      shid_q  <= shid_d;
      flag0_q <= flag0_d;
      gcnt_q <= gcnt_d;
      statedb_wr_select_q <= statedb_wr_select_d;
    end

  prim_intr_hw #(.Width(1)) intr_hw_cs_cmd_req_done (
    .event_intr_i           (event_cs_cmd_req_done),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cs_cmd_req_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cs_cmd_req_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cs_cmd_req_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cs_cmd_req_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cs_cmd_req_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cs_cmd_req_done.d),
    .intr_o                 (intr_cs_cmd_req_done_o)
  );


  prim_intr_hw #(.Width(1)) intr_hw_cs_fifo_err (
    .event_intr_i           (event_cs_fifo_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cs_fifo_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cs_fifo_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cs_fifo_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cs_fifo_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cs_fifo_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cs_fifo_err.d),
    .intr_o                 (intr_cs_fifo_err_o)
  );

  // set the interrupt sources
  assign event_cs_fifo_err =
         (|cmd_stage_err) ||
         state_db_fifo_err ||
         ctr_drbg_cmd_fifo_err ||
         ctr_drbg_upd_fifo_err ||
         ctr_drbg_gen_fifo_err ||
         block_encrypt_fifo_err ||
         sfifo_pentr_err ||
         sfifo_entr_err; // TODO: add all fifo errors

  // master module enable
  assign cs_enable = reg2hw.cs_ctrl.cs_enable.q;
  assign aes_cipher_enable = reg2hw.cs_ctrl.aes_cipher_enable.q;
  // fifo selection for debug
  assign fifo_sel = reg2hw.cs_ctrl.fifo_depth_sts_sel.q;


  //------------------------------------------
  // application interface
  //------------------------------------------

  genvar ai; // app i/f
  generate    for (ai = 0; ai < NApps; ai = ai+1) begin : g_cmd_stage

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
           .cmd_arb_sop_o       (cmd_arb_sop[ai]),
           .cmd_arb_mop_o       (cmd_arb_mop[ai]),
           .cmd_arb_eop_o       (cmd_arb_eop[ai]),
           .cmd_arb_gnt_i       (cmd_arb_gnt[ai]),
           .cmd_arb_bus_o       (cmd_arb_bus[ai]),
           .cmd_ack_i           (cmd_core_ack[ai]),
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
  assign cmd_stage_vld[NApps-1] = reg2hw.cs_cmd_req.qe;
  assign cmd_stage_bus[NApps-1] = reg2hw.cs_cmd_req.q;
  assign hw2reg.cs_cmd_sts.cmd_rdy.de = 1'b1;
  assign hw2reg.cs_cmd_sts.cmd_rdy.d = cmd_stage_rdy[NApps-1];
  // cmd ack
  assign hw2reg.cs_cmd_sts.cmd_ack.de = cmd_stage_ack[NApps-1];
  assign hw2reg.cs_cmd_sts.cmd_ack.d = 1'b1;
  assign hw2reg.cs_cmd_sts.cmd_sts.de = cmd_stage_ack[NApps-1];
  assign hw2reg.cs_cmd_sts.cmd_sts.d = cmd_stage_ack_sts[NApps-1];
  // genbits
  assign hw2reg.cs_genbits_vld.d = genbits_stage_vld_sw;

  assign hw2reg.cs_genbits.d = efuse_sw_app_enable_i ? genbits_stage_bus_sw : '0;

  // TODO: get packer working
  // pack the gen bits into a 32 bit register sized word
  prim_packer # (.InW(BlkLen),.OutW(32))
    u_prim_packer_sw_genbits (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .valid_i        (genbits_stage_vld[NApps-1]),
    .data_i         (genbits_stage_bus[NApps-1]),
    .mask_i         ({BlkLen{1'b1}}),
    .ready_o        (genbits_stage_rdy[NApps-1]),
    .valid_o        (genbits_stage_vld_sw),
    .data_o         (genbits_stage_bus_sw),
    .mask_o         (),
    .ready_i        (1'b1),
    .flush_i        (1'b0), // !cs_enable),
    .flush_done_o   ()
  );

  // HW interface connections (up to 16, numbered 0-14)
  genvar hai; // hw app i/f
  generate
    for (hai = 0; hai < (NApps-1); hai = hai+1) begin : g_app_if
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

  // create control bus for commands
  assign acmd_sop = (|cmd_arb_sop);
  assign acmd_mop = (|cmd_arb_mop);
  assign acmd_eop = (|cmd_arb_eop);

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
  assign flag0 = acmd_bus[12];
  assign gcnt = acmd_bus[31:16];

  assign acmd_d = acmd_sop ? acmd : acmd_q;
  assign shid_d = acmd_sop ? shid : shid_q;
  assign flag0_d = acmd_sop ? flag0 : flag0_q;
  assign gcnt_d = acmd_sop ? gcnt : gcnt_q;

  // sm to process all instantiation requests
  csrng_main_sm
    u_csrng_main_sm
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .acmd_avail_i(acmd_avail),
       .acmd_accept_o(acmd_accept),
       .acmd_i(acmd),
       .acmd_eop_i(acmd_eop),
       .ctr_drbg_cmd_req_rdy_i(ctr_drbg_cmd_req_rdy),
       .flag0_i(flag0),
       .cmd_entropy_avail_i(cmd_entropy_avail),
       .instant_req_o(instant_req),
       .reseed_req_o(reseed_req),
       .generate_req_o(generate_req),
       .update_req_o(update_req),
       .uninstant_req_o(uninstant_req)
       );


  // interrupt for sw app interface only
  assign event_cs_cmd_req_done = cmd_core_ack[NApps-1];

  genvar csi; // command stage i/f
  generate
    for (csi = 0; csi < NApps; csi = csi+1) begin : g_cmd_ack
      assign cmd_core_ack[csi] = state_db_sts_ack && (state_db_sts_id == csi);
      assign cmd_core_ack_sts[csi] = state_db_sts_code;
      assign genbits_core_vld[csi] = gen_result_wr_req;
      assign genbits_core_bus[csi] = gen_result_bits;
    end
  endgenerate


  // pack the additional data from the cmd
  prim_packer # (.InW(32),.OutW(SeedLen))
    u_prim_packer_adata (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .valid_i        (acmd_mop),
    .data_i         (acmd_bus),
    .mask_i         ({32{1'b1}}),
    .ready_o        (),
    .valid_o        (), // packer_adata_vld),
    .data_o         (packer_adata),
    .mask_o         (),
    .ready_i        (1'b1),
    .flush_i        (1'b0), // !cs_enable),
    .flush_done_o   ()
  );


  //-------------------------------------
  // csrng_state_db nstantiation
  //-------------------------------------

  assign state_db_rd_req = reseed_req || generate_req || update_req;

  assign cmd_result_wr_req = cmd_result_ack && (cmd_result_ccmd != GEN);

  csrng_state_db #(.NApps(NApps),
                   .StateId(StateId),
                   .BlkLen(BlkLen),
                   .KeyLen(KeyLen),
                   .CtrLen(CtrLen))
    u_csrng_state_db
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .state_db_enable_i(cs_enable),
       .state_db_rd_req_i(state_db_rd_req),
       .state_db_rd_inst_id_i(shid_q),
       .state_db_rd_key_o(state_db_rd_key),
       .state_db_rd_v_o(state_db_rd_v),
       .state_db_rd_res_ctr_o(state_db_rd_rc),

       .state_db_wr_req_i(state_db_wr_req),
       .state_db_wr_req_rdy_o(state_db_wr_req_rdy),
       .state_db_wr_inst_id_i(state_db_wr_inst_id),
       .state_db_wr_key_i(state_db_wr_key),
       .state_db_wr_v_i(state_db_wr_v),
       .state_db_wr_res_ctr_i(state_db_wr_rc),
       .state_db_wr_sts_code_i(state_db_wr_sts_code),

       .state_db_sts_rdy_i(1'b1),
       .state_db_sts_ack_o(state_db_sts_ack),
       .state_db_sts_code_o(state_db_sts_code),
       .state_db_sts_id_o(state_db_sts_id),
       .state_db_fifo_err_o(state_db_fifo_err)
       );

  assign statedb_wr_select_d = !statedb_wr_select_q;
  assign cmd_blk_select = !statedb_wr_select_q;
  assign gen_blk_select =  statedb_wr_select_q;

  // return to requesting block
  assign cmd_result_ack_rdy = cmd_blk_select && state_db_wr_req_rdy;
  assign gen_result_ack_rdy = gen_blk_select && state_db_wr_req_rdy;

  // muxes for statedb block inputs
  assign state_db_wr_req = gen_blk_select ? gen_result_wr_req : cmd_result_wr_req;
  assign state_db_wr_inst_id = gen_blk_select ? gen_result_inst_id : cmd_result_inst_id;
  assign state_db_wr_key = gen_blk_select ? gen_result_key : cmd_result_key;
  assign state_db_wr_v = gen_blk_select ? gen_result_v : cmd_result_v;
  assign state_db_wr_rc = gen_blk_select ? gen_result_rc : cmd_result_rc;
  assign state_db_wr_sts_code = gen_blk_select ? gen_result_ack_sts : cmd_result_ack_sts;


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

  assign sfifo_entr_push = cs_enable && entropy_src_hw_if_i.entropy_src_vld;
  assign sfifo_entr_pop = cs_enable && sfifo_entr_not_empty && sfifo_pentr_avail;

  // fifo err
  assign sfifo_entr_err =
         (sfifo_entr_push && !sfifo_entr_not_full) ||
         (sfifo_entr_pop && !sfifo_entr_not_empty);


  // pack the entropy data from the entr fifo
  prim_packer # (.InW(32),.OutW(SeedLen))
    u_prim_packer_entropy (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .valid_i        (sfifo_entr_pop),
    .data_i         (sfifo_entr_rdata),
    .mask_i         ({32{1'b1}}),
    .ready_o        (),
    .valid_o        (packer_entropy_vld),
    .data_o         (sfifo_pentr_wdata),
    .mask_o         (),
    .ready_i        (1'b1),
    .flush_i        (1'b0), // !cs_enable),
    .flush_done_o   ()
  );


  prim_fifo_sync # (.Width(SeedLen),.Pass(0),.Depth(PEntrFifoDepth))
    u_prim_fifo_sync_pentr
      (
       .clk_i          (clk_i),
       .rst_ni         (rst_ni),
       .clr_i          (!cs_enable),
       .wvalid         (sfifo_pentr_push),
       .wready         (sfifo_pentr_not_full),
       .wdata          (sfifo_pentr_wdata),
       .rvalid         (sfifo_pentr_not_empty),
       .rready         (sfifo_pentr_pop),
       .rdata          (sfifo_pentr_rdata),
       .depth          (sfifo_pentr_depth)
       );

  // allow one extra location because of packer
  assign sfifo_pentr_avail = (sfifo_pentr_depth < (PEntrFifoDepth-1));

  assign sfifo_pentr_push = cs_enable && packer_entropy_vld;
  assign sfifo_pentr_pop = (instant_req || reseed_req);

  // fifo err
  assign sfifo_pentr_err =
         (sfifo_pentr_push && !sfifo_pentr_not_full) ||
         (sfifo_pentr_pop && !sfifo_pentr_not_empty);


  assign cmd_entropy_avail = !sfifo_pentr_not_empty;
  assign cmd_entropy =
         (instant_req && !flag0_q) ? sfifo_pentr_rdata :
         generate_req ? {{SeedLen-16{1'b0}},gcnt} :
         '0;

  //-------------------------------------
  // csrng_ctr_drbg_cmd instantiation
  //-------------------------------------

  assign ctr_drbg_cmd_req =
         instant_req ||reseed_req || generate_req || update_req || uninstant_req;


  csrng_ctr_drbg_cmd #(.Cmd(Cmd),
                       .StateId(StateId),
                       .BlkLen(BlkLen),
                       .KeyLen(KeyLen),
                       .SeedLen(SeedLen),
                       .CtrLen(CtrLen))
    u_csrng_ctr_drbg_cmd
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .ctr_drbg_cmd_enable_i(cs_enable),
       .ctr_drbg_cmd_req_i(ctr_drbg_cmd_req),
       .ctr_drbg_cmd_rdy_o(ctr_drbg_cmd_req_rdy),
       .ctr_drbg_cmd_ccmd_i(acmd_q),
       .ctr_drbg_cmd_inst_id_i(shid_q),
       .ctr_drbg_cmd_entropy_i(cmd_entropy), // TODO: fix x's
       .ctr_drbg_cmd_adata_i(packer_adata),
       .ctr_drbg_cmd_key_i(state_db_rd_key),
       .ctr_drbg_cmd_v_i(state_db_rd_v),
       .ctr_drbg_cmd_rc_i(state_db_rd_rc),

       .ctr_drbg_cmd_ack_o(cmd_result_ack),
       .ctr_drbg_cmd_sts_o(cmd_result_ack_sts),
       .ctr_drbg_cmd_rdy_i(cmd_result_ack_rdy),
       .ctr_drbg_cmd_ccmd_o(cmd_result_ccmd),
       .ctr_drbg_cmd_inst_id_o(cmd_result_inst_id),
       .ctr_drbg_cmd_key_o(cmd_result_key),
       .ctr_drbg_cmd_v_o(cmd_result_v),
       .ctr_drbg_cmd_rc_o(cmd_result_rc),
       .ctr_drbg_cmd_gcnt_o(cmd_result_gcnt),

       // interface to updblk from cmdblk
       .cmd_upd_req_o(cmdblk_updblk_arb_req),
       .upd_cmd_rdy_i(updblk_cmdblk_arb_req_rdy),
       .cmd_upd_ccmd_o(cmdblk_updblk_ccmd_arb_din),
       .cmd_upd_inst_id_o(cmdblk_updblk_id_arb_din),
       .cmd_upd_pdata_o(cmdblk_updblk_pdata_arb_din),
       .cmd_upd_key_o(cmdblk_updblk_key_arb_din),
       .cmd_upd_v_o(cmdblk_updblk_v_arb_din),

       .upd_cmd_ack_i(updblk_cmdblk_ack),
       .cmd_upd_rdy_o(cmdblk_updblk_ack_rdy),
       .upd_cmd_ccmd_i(updblk_ccmd),
       .upd_cmd_inst_id_i(updblk_inst_id),
       .upd_cmd_key_i(updblk_key),
       .upd_cmd_v_i(updblk_v),

       .ctr_drbg_cmd_fifo_err_o(ctr_drbg_cmd_fifo_err)
       );


  //-------------------------------------
  // csrng_ctr_drbg_upd instantiation
  //-------------------------------------


  csrng_ctr_drbg_upd #(.Cmd(Cmd),
                       .StateId(StateId),
                       .BlkLen(BlkLen),
                       .KeyLen(KeyLen),
                       .SeedLen(SeedLen),
                       .CtrLen(CtrLen))
    u_csrng_ctr_drbg_upd
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .ctr_drbg_upd_enable_i(cs_enable),
       .ctr_drbg_upd_req_i(updblk_arb_vld),
       .ctr_drbg_upd_rdy_o(updblk_arb_rdy),
       .ctr_drbg_upd_ack_o(updblk_ack),
       .ctr_drbg_upd_rdy_i(updblk_ack_rdy),
       .ctr_drbg_upd_ccmd_i(updblk_arb_ccmd),
       .ctr_drbg_upd_inst_id_i(updblk_arb_inst_id),
       .ctr_drbg_upd_pdata_i(updblk_arb_pdata),
       .ctr_drbg_upd_key_i(updblk_arb_key),
       .ctr_drbg_upd_v_i(updblk_arb_v),
       .ctr_drbg_upd_ccmd_o(updblk_ccmd),
       .ctr_drbg_upd_inst_id_o(updblk_inst_id),
       .ctr_drbg_upd_key_o(updblk_key),
       .ctr_drbg_upd_v_o(updblk_v),

       .block_encrypt_req_o(updblk_benblk_arb_req),
       .block_encrypt_rdy_i(updblk_benblk_arb_req_rdy),
       .block_encrypt_ccmd_o(updblk_benblk_cmd_arb_din),
       .block_encrypt_inst_id_o(updblk_benblk_id_arb_din),
       .block_encrypt_key_o(updblk_benblk_key_arb_din),
       .block_encrypt_v_o(updblk_benblk_v_arb_din),
       .block_encrypt_ack_i(benblk_updblk_ack),
       .block_encrypt_rdy_o(updblk_benblk_ack_rdy),
       .block_encrypt_ccmd_i(benblk_cmd),
       .block_encrypt_inst_id_i(benblk_inst_id),
       .block_encrypt_v_i(benblk_v),
       .ctr_drbg_upd_fifo_err_o(ctr_drbg_upd_fifo_err)
       );

  // update block  arbiter

  prim_arbiter_ppc #(
                     .N(NumUpdateReqs), // (cmd req and gen req)
                     .DW(UpdateArbWidth))    // Data width
    u_prim_arbiter_ppc_updblk_arb
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .req_i({genblk_updblk_arb_req,cmdblk_updblk_arb_req}),
       .data_i(updblk_arb_din),
       .gnt_o({updblk_genblk_arb_req_rdy,updblk_cmdblk_arb_req_rdy}),
       .idx_o(),
       .valid_o(updblk_arb_vld),
       .data_o(updblk_arb_data),
       .ready_i(updblk_arb_rdy)
       );

  assign updblk_arb_din[0] = {cmdblk_updblk_key_arb_din,cmdblk_updblk_v_arb_din,
                              cmdblk_updblk_pdata_arb_din,
                              cmdblk_updblk_id_arb_din,cmdblk_updblk_ccmd_arb_din};

  assign updblk_arb_din[1] = {genblk_updblk_key_arb_din,genblk_updblk_v_arb_din,
                              genblk_updblk_pdata_arb_din,
                              genblk_updblk_id_arb_din,genblk_updblk_ccmd_arb_din};

  assign {updblk_arb_key,updblk_arb_v,updblk_arb_pdata,
          updblk_arb_inst_id,updblk_arb_ccmd} = updblk_arb_data;

  assign updblk_cmdblk_ack = (updblk_ack && (updblk_ccmd != GEN)); // TODO: add new PGEN decode
  assign updblk_genblk_ack = (updblk_ack && (updblk_ccmd == GEN));

  assign updblk_ack_rdy = (updblk_ccmd == GEN) ? genblk_updblk_ack_rdy : cmdblk_updblk_ack_rdy;


  //-------------------------------------
  // csrng_block_encrypt instantiation
  //-------------------------------------

  csrng_block_encrypt #(
                       .Cmd(Cmd),
                       .StateId(StateId),
                       .BlkLen(BlkLen),
                       .KeyLen(KeyLen))
    u_csrng_block_encrypt
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .block_encrypt_bypass_i(!aes_cipher_enable),
       .block_encrypt_enable_i(cs_enable),
       .block_encrypt_req_i(benblk_arb_vld),
       .block_encrypt_rdy_o(benblk_arb_rdy),
       .block_encrypt_key_i(benblk_arb_key),
       .block_encrypt_v_i(benblk_arb_v),
       .block_encrypt_cmd_i(benblk_arb_cmd),
       .block_encrypt_id_i(benblk_arb_inst_id),
       .block_encrypt_ack_o(benblk_ack),
       .block_encrypt_rdy_i(benblk_ack_rdy),
       .block_encrypt_cmd_o(benblk_cmd),
       .block_encrypt_id_o(benblk_inst_id),
       .block_encrypt_v_o(benblk_v),
       .block_encrypt_fifo_err_o(block_encrypt_fifo_err)
       );


  prim_arbiter_ppc #(
                     .N(NumBlkEncReqs), // (upd req and gen req)
                     .DW(BlkEncArbWidth))    // Data width
    u_prim_arbiter_ppc_benblk_arb
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .req_i({genblk_benblk_arb_req,updblk_benblk_arb_req}),
       .data_i(benblk_arb_din),
       .gnt_o({genblk_benblk_arb_req_rdy,updblk_benblk_arb_req_rdy}), // blk_enc_arb_req_rdy_out),
       .idx_o(),
       .valid_o(benblk_arb_vld),
       .data_o(benblk_arb_data),
       .ready_i(benblk_arb_rdy)
       );

  assign benblk_arb_din[0] = {updblk_benblk_key_arb_din,updblk_benblk_v_arb_din,
                              updblk_benblk_id_arb_din,updblk_benblk_cmd_arb_din};
  assign benblk_arb_din[1] = {genblk_benblk_key_arb_din,genblk_benblk_v_arb_din,
                              genblk_benblk_id_arb_din,genblk_benblk_cmd_arb_din};

  assign benblk_updblk_ack = (benblk_ack && (benblk_cmd != GEN));
  assign benblk_genblk_ack = (benblk_ack && (benblk_cmd == GEN));

  assign benblk_ack_rdy = (benblk_cmd == GEN) ? genblk_benblk_ack_rdy : updblk_benblk_ack_rdy;

  assign {benblk_arb_key,benblk_arb_v,benblk_arb_inst_id,benblk_arb_cmd} = benblk_arb_data;


  //-------------------------------------
  // csrng_ctr_drbg_gen instantiation
  //-------------------------------------

  assign ctr_drbg_gen_req = cmd_result_ack && (cmd_result_ccmd == GEN);


  csrng_ctr_drbg_gen #(.Cmd(Cmd),
                       .StateId(StateId),
                       .BlkLen(BlkLen),
                       .KeyLen(KeyLen),
                       .SeedLen(SeedLen),
                       .CtrLen(CtrLen))
    u_csrng_ctr_drbg_gen
      (
       .clk_i(clk_i),
       .rst_ni(rst_ni),
       .ctr_drbg_gen_enable_i(cs_enable),
       .ctr_drbg_gen_req_i(ctr_drbg_gen_req),
       .ctr_drbg_gen_rdy_o(), // TODO: need this?->ctr_drbg_cmd_req_rdy),
       .ctr_drbg_gen_ccmd_i(cmd_result_ccmd),
       .ctr_drbg_gen_inst_id_i(cmd_result_inst_id),
       .ctr_drbg_gen_adata_i(cmd_entropy), // TODO: stub, need to add support to cmd block
       .ctr_drbg_gen_key_i(cmd_result_key),
       .ctr_drbg_gen_v_i(cmd_result_v),
       .ctr_drbg_gen_rc_i(cmd_result_rc),
       .ctr_drbg_gen_gcnt_i(cmd_result_gcnt),

       .ctr_drbg_gen_ack_o(gen_result_wr_req),
       .ctr_drbg_gen_sts_o(gen_result_ack_sts),
       .ctr_drbg_gen_rdy_i(gen_result_ack_rdy),
       .ctr_drbg_gen_ccmd_o(), // NC
       .ctr_drbg_gen_inst_id_o(gen_result_inst_id),
       .ctr_drbg_gen_key_o(gen_result_key),
       .ctr_drbg_gen_v_o(gen_result_v),
       .ctr_drbg_gen_rc_o(gen_result_rc),
       .ctr_drbg_gen_bits_o(gen_result_bits),

       // interface to updblk from genblk
       .gen_upd_req_o(genblk_updblk_arb_req),
       .upd_gen_rdy_i(updblk_genblk_arb_req_rdy),
       .gen_upd_ccmd_o(genblk_updblk_ccmd_arb_din),
       .gen_upd_inst_id_o(genblk_updblk_id_arb_din),
       .gen_upd_pdata_o(genblk_updblk_pdata_arb_din),
       .gen_upd_key_o(genblk_updblk_key_arb_din),
       .gen_upd_v_o(genblk_updblk_v_arb_din),

       .upd_gen_ack_i(updblk_genblk_ack),
       .gen_upd_rdy_o(genblk_updblk_ack_rdy),
       .upd_gen_ccmd_i(updblk_ccmd),
       .upd_gen_inst_id_i(updblk_inst_id),
       .upd_gen_key_i(updblk_key),
       .upd_gen_v_i(updblk_v),

       .block_encrypt_req_o(genblk_benblk_arb_req),
       .block_encrypt_rdy_i(genblk_benblk_arb_req_rdy),
       .block_encrypt_ccmd_o(genblk_benblk_cmd_arb_din),
       .block_encrypt_inst_id_o(genblk_benblk_id_arb_din),
       .block_encrypt_key_o(genblk_benblk_key_arb_din),
       .block_encrypt_v_o(genblk_benblk_v_arb_din),
       .block_encrypt_ack_i(benblk_genblk_ack),
       .block_encrypt_rdy_o(genblk_benblk_ack_rdy),
       .block_encrypt_ccmd_i(benblk_cmd),
       .block_encrypt_inst_id_i(benblk_inst_id),
       .block_encrypt_v_i(benblk_v),

       .ctr_drbg_gen_fifo_err_o(ctr_drbg_gen_fifo_err)
       );



  //--------------------------------------------
  // report csrng request summary
  //--------------------------------------------

  assign     hw2reg.cs_sum_sts.fifo_depth_sts.de = cs_enable;
  assign     hw2reg.cs_sum_sts.fifo_depth_sts.d  =
             (fifo_sel == 4'h0) ? {{(24-$clog2(EntrFifoDepth)){1'b0}},sfifo_entr_depth} : 
             24'b0;


  assign     hw2reg.cs_sum_sts.diag.de = ~cs_enable;
  assign     hw2reg.cs_sum_sts.diag.d  =
                                        (reg2hw.cs_regen)          || // not used
                                        (|reg2hw.cs_genbits.q)     || // not used
                                        (reg2hw.cs_genbits.re)     || // not used
                                        (|genbits_core_rdy);          // TODO: unfinished



endmodule
