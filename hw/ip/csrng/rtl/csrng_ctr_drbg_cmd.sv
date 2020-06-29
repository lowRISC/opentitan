// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng ctr_drbg commands module
//
// Accepts all csrng commands

module csrng_ctr_drbg_cmd #(
  parameter int unsigned Cmd = 3,
  parameter int unsigned StateId = 4,
  parameter int unsigned BlkLen = 128,
  parameter int unsigned KeyLen = 256,
  parameter int unsigned SeedLen = 384,
  parameter int unsigned CtrLen  = 32s
) (
  input                  clk_i,
  input                  rst_ni,

   // command interface
  input logic                ctr_drbg_cmd_enable_i,
  input logic                ctr_drbg_cmd_req_i,
  output logic               ctr_drbg_cmd_rdy_o, // ready to process the req above
  input logic [Cmd-1:0]      ctr_drbg_cmd_ccmd_i,    // current command
  input logic [StateId-1:0]  ctr_drbg_cmd_inst_id_i, // instantance id
  input logic [SeedLen-1:0]  ctr_drbg_cmd_entropy_i, // es entropy
  input logic [SeedLen-1:0]  ctr_drbg_cmd_adata_i,   // additional data
  input logic [KeyLen-1:0]   ctr_drbg_cmd_key_i,
  input logic [BlkLen-1:0]   ctr_drbg_cmd_v_i,
  input logic [CtrLen-1:0]   ctr_drbg_cmd_rc_i,

  output logic               ctr_drbg_cmd_ack_o, // final ack when update process has been completed
  output logic [1:0]         ctr_drbg_cmd_sts_o, // final ack status
  input logic                ctr_drbg_cmd_rdy_i, // ready to process the ack above
  output logic [Cmd-1:0]     ctr_drbg_cmd_ccmd_o,
  output logic [StateId-1:0] ctr_drbg_cmd_inst_id_o,
//  output logic [SeedLen-1:0]  ctr_drbg_cmd_adata_o, TODO: add for gen cmd support
  output logic [KeyLen-1:0]  ctr_drbg_cmd_key_o,
  output logic [BlkLen-1:0]  ctr_drbg_cmd_v_o,
  output logic [CtrLen-1:0]  ctr_drbg_cmd_rc_o,
  output logic [15:0]        ctr_drbg_cmd_gcnt_o,
   // update interface
  output logic               cmd_upd_req_o,
  input logic                upd_cmd_rdy_i,
  output logic [Cmd-1:0]     cmd_upd_ccmd_o,
  output logic [StateId-1:0] cmd_upd_inst_id_o,
  output logic [SeedLen-1:0] cmd_upd_pdata_o,
  output logic [KeyLen-1:0]  cmd_upd_key_o,
  output logic [BlkLen-1:0]  cmd_upd_v_o,

  input logic                upd_cmd_ack_i,
  output logic               cmd_upd_rdy_o,
  input logic [Cmd-1:0]      upd_cmd_ccmd_i,
  input logic [StateId-1:0]  upd_cmd_inst_id_i,
  input logic [KeyLen-1:0]   upd_cmd_key_i,
  input logic [BlkLen-1:0]   upd_cmd_v_i,
  // misc
  output logic               ctr_drbg_cmd_fifo_err_o
);

  localparam CmdreqFifoDepth = 2;
  localparam CmdreqFifoWidth = KeyLen+BlkLen+CtrLen+2*SeedLen+StateId+Cmd;
  localparam RCStageFifoDepth = 16;
  localparam RCStageFifoWidth = CtrLen+16+Cmd;
  localparam KeyVRCFifoDepth = 2;
  localparam KeyVRCFifoWidth = KeyLen+BlkLen+CtrLen+16+StateId+Cmd;

  typedef enum logic [2:0] {
                            INS = 3'h0,
                            RES = 3'h1,
                            GEN = 3'h2,
                            UPD = 3'h3,
                            UNI = 3'h4
                            } acmd_e;

  // signals
  logic [Cmd-1:0]     cmdreq_ccmd;
  logic [StateId-1:0] cmdreq_id;
  logic [SeedLen-1:0] cmdreq_entropy;
  logic [SeedLen-1:0] cmdreq_adata;
  logic [KeyLen-1:0]  cmdreq_key;
  logic [BlkLen-1:0]  cmdreq_v;
  logic [CtrLen-1:0]  cmdreq_rc;

  logic [SeedLen-1:0] prep_seed_material;
  logic [KeyLen-1:0]  prep_key;
  logic [BlkLen-1:0]  prep_v;
  logic [CtrLen-1:0]  prep_rc;
  logic [15:0]        prep_gcnt;
  logic [CtrLen-1:0]  rcstage_rc;
  logic [Cmd-1:0]     rcstage_ccmd;
  logic [15:0]        rcstage_gcnt;

  // cmdreq fifo
  // logic [$clog2(CmdreqFifoDepth):0] sfifo_cmdreq_depth;
  logic [CmdreqFifoWidth-1:0] sfifo_cmdreq_rdata;
  logic                       sfifo_cmdreq_push;
  logic [CmdreqFifoWidth-1:0]  sfifo_cmdreq_wdata;
  logic                       sfifo_cmdreq_pop;
  logic                       sfifo_cmdreq_err;
  logic                       sfifo_cmdreq_not_full;
  logic                       sfifo_cmdreq_not_empty;

  // rcstage fifo
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_rdata;
  logic                        sfifo_rcstage_push;
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_wdata;
  logic                        sfifo_rcstage_pop;
  logic                        sfifo_rcstage_err;
  logic                        sfifo_rcstage_not_full;
  logic                        sfifo_rcstage_not_empty;

  // keyvrc fifo
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_rdata;
  logic                        sfifo_keyvrc_push;
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_wdata;
  logic                        sfifo_keyvrc_pop;
  logic                        sfifo_keyvrc_err;
  logic                        sfifo_keyvrc_not_full;
  logic                        sfifo_keyvrc_not_empty;


//  // flops
//  logic [1:0]         ctr_drbg_cmd_sts_q, ctr_drbg_cmd_sts_d;
//
//  always_ff @(posedge clk_i or negedge rst_ni)
//    if (!rst_ni) begin
//      ctr_drbg_cmd_sts_q <= '0;
//    end else begin
//      ctr_drbg_cmd_sts_q <= ctr_drbg_cmd_sts_d;
//    end

  // error signal
  assign ctr_drbg_cmd_fifo_err_o =
                                  sfifo_cmdreq_err ||
                                  sfifo_rcstage_err ||
                                  sfifo_keyvrc_err;

  //--------------------------------------------
  // input request fifo for staging cmd request
  //--------------------------------------------

  prim_fifo_sync # (.Width(CmdreqFifoWidth),.Pass(0),.Depth(CmdreqFifoDepth))
    u_prim_fifo_sync_cmdreq
      (
       .clk_i          (clk_i),
       .rst_ni         (rst_ni),
       .clr_i          (!ctr_drbg_cmd_enable_i),
       .wvalid         (sfifo_cmdreq_push),
       .wready         (sfifo_cmdreq_not_full),
       .wdata          (sfifo_cmdreq_wdata),
       .rvalid         (sfifo_cmdreq_not_empty),
       .rready         (sfifo_cmdreq_pop),
       .rdata          (sfifo_cmdreq_rdata),
       .depth          ()
       );

  assign sfifo_cmdreq_wdata = {ctr_drbg_cmd_key_i,ctr_drbg_cmd_v_i,ctr_drbg_cmd_rc_i,
                               ctr_drbg_cmd_entropy_i,ctr_drbg_cmd_adata_i,
                               ctr_drbg_cmd_inst_id_i,ctr_drbg_cmd_ccmd_i};

  assign sfifo_cmdreq_push = ctr_drbg_cmd_enable_i && ctr_drbg_cmd_req_i;

  assign sfifo_cmdreq_pop = ctr_drbg_cmd_enable_i && upd_cmd_rdy_i && sfifo_cmdreq_not_empty;

  assign {cmdreq_key,cmdreq_v,cmdreq_rc,
          cmdreq_entropy,cmdreq_adata,
          cmdreq_id,cmdreq_ccmd} = sfifo_cmdreq_rdata;

  assign ctr_drbg_cmd_rdy_o = sfifo_cmdreq_not_full;

  assign sfifo_cmdreq_err =
         (sfifo_cmdreq_push && !sfifo_cmdreq_not_full) ||
         (sfifo_cmdreq_pop && !sfifo_cmdreq_not_empty);


  //--------------------------------------------
  // prepare values for update step
  //--------------------------------------------

  assign prep_seed_material =
         (cmdreq_ccmd == INS) ? (cmdreq_entropy ^ cmdreq_adata) :
         (cmdreq_ccmd == RES) ? (cmdreq_entropy ^ cmdreq_adata) :
         (cmdreq_ccmd == GEN) ? cmdreq_adata :
         (cmdreq_ccmd == UPD) ? cmdreq_adata :
         '0;

  assign prep_key =
         (cmdreq_ccmd == INS) ? {KeyLen{1'b0}} :
         (cmdreq_ccmd == RES) ? cmdreq_key :
         (cmdreq_ccmd == GEN) ? cmdreq_key :
         (cmdreq_ccmd == UPD) ? cmdreq_key :
         '0;

  assign prep_v =
         (cmdreq_ccmd == INS) ? {BlkLen{1'b0}} :
         (cmdreq_ccmd == RES) ? cmdreq_v :
         (cmdreq_ccmd == GEN) ? cmdreq_v :
         (cmdreq_ccmd == UPD) ? cmdreq_v :
         '0;

  assign prep_rc =
         (cmdreq_ccmd == INS) ? {{(CtrLen-1){1'b0}},1'b1} :
         (cmdreq_ccmd == RES) ? {{(CtrLen-1){1'b0}},1'b1} :
         (cmdreq_ccmd == GEN) ? cmdreq_rc :
         (cmdreq_ccmd == UPD) ? cmdreq_rc :
         '0;

  // for generate entropy count, use the lower 16 bits of the entropy field
  assign prep_gcnt =
         (cmdreq_ccmd == GEN) ? cmdreq_entropy[15:0] :
         '0;

  // send to the update block
  assign cmd_upd_req_o = sfifo_cmdreq_not_empty;
  assign cmd_upd_ccmd_o = cmdreq_ccmd;
  assign cmd_upd_inst_id_o = cmdreq_id;
  assign cmd_upd_pdata_o = prep_seed_material;
  assign cmd_upd_key_o = prep_key;
  assign cmd_upd_v_o = prep_v;



  //--------------------------------------------
  // fifo to stage rc and command, waiting for update block to ack
  //--------------------------------------------

  prim_fifo_sync # (.Width(RCStageFifoWidth),.Pass(0),.Depth(RCStageFifoDepth))
    u_prim_fifo_sync_rcstage
      (
       .clk_i          (clk_i),
       .rst_ni         (rst_ni),
       .clr_i          (!ctr_drbg_cmd_enable_i),
       .wvalid         (sfifo_rcstage_push),
       .wready         (sfifo_rcstage_not_full),
       .wdata          (sfifo_rcstage_wdata),
       .rvalid         (sfifo_rcstage_not_empty),
       .rready         (sfifo_rcstage_pop),
       .rdata          (sfifo_rcstage_rdata),
       .depth          ()
       );

  assign sfifo_rcstage_push = sfifo_cmdreq_pop;
  assign sfifo_rcstage_wdata = {prep_rc,prep_gcnt,cmdreq_ccmd};
  assign sfifo_rcstage_pop = sfifo_rcstage_not_empty && upd_cmd_ack_i;
  assign {rcstage_rc,rcstage_gcnt,rcstage_ccmd} = sfifo_rcstage_rdata;


  assign sfifo_rcstage_err =
         (sfifo_rcstage_push && !sfifo_rcstage_not_full) ||
         (sfifo_rcstage_pop && !sfifo_rcstage_not_empty);

  assign cmd_upd_rdy_o = sfifo_rcstage_not_empty && sfifo_keyvrc_not_full;

  //--------------------------------------------
  // final cmd block processing
  //--------------------------------------------

  prim_fifo_sync # (.Width(KeyVRCFifoWidth),.Pass(0),.Depth(KeyVRCFifoDepth))
    u_prim_fifo_sync_keyvrc
      (
       .clk_i          (clk_i),
       .rst_ni         (rst_ni),
       .clr_i          (!ctr_drbg_cmd_enable_i),
       .wvalid         (sfifo_keyvrc_push),
       .wready         (sfifo_keyvrc_not_full),
       .wdata          (sfifo_keyvrc_wdata),
       .rvalid         (sfifo_keyvrc_not_empty),
       .rready         (sfifo_keyvrc_pop),
       .rdata          (sfifo_keyvrc_rdata),
       .depth          ()
       );

  assign sfifo_keyvrc_push = sfifo_rcstage_pop;

  assign sfifo_keyvrc_wdata = (rcstage_ccmd == UNI) ?
         {{(KeyLen+BlkLen+CtrLen+16){1'b0}},upd_cmd_inst_id_i,upd_cmd_ccmd_i} :
         {upd_cmd_key_i,upd_cmd_v_i,rcstage_rc,rcstage_gcnt,upd_cmd_inst_id_i,upd_cmd_ccmd_i};

  assign sfifo_keyvrc_pop = ctr_drbg_cmd_rdy_i && sfifo_keyvrc_not_empty;
  assign {ctr_drbg_cmd_key_o,ctr_drbg_cmd_v_o,ctr_drbg_cmd_rc_o,ctr_drbg_cmd_gcnt_o,
          ctr_drbg_cmd_inst_id_o,ctr_drbg_cmd_ccmd_o} = sfifo_keyvrc_rdata;

  assign sfifo_keyvrc_err =
         (sfifo_keyvrc_push && !sfifo_keyvrc_not_full) ||
         (sfifo_keyvrc_pop && !sfifo_keyvrc_not_empty);

  // block ack
  assign ctr_drbg_cmd_ack_o = sfifo_keyvrc_pop;
//  assign ctr_drbg_cmd_sts_d = 2'b0; // TODO: always zero?
//  assign ctr_drbg_cmd_sts_o = ctr_drbg_cmd_sts_q;
  assign ctr_drbg_cmd_sts_o = 2'b0;


endmodule
