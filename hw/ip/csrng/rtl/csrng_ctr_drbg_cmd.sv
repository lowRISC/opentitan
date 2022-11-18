// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng ctr_drbg commands module
//
// Accepts all csrng commands

module csrng_ctr_drbg_cmd import csrng_pkg::*; #(
  parameter int Cmd = 3,
  parameter int StateId = 4,
  parameter int BlkLen = 128,
  parameter int KeyLen = 256,
  parameter int SeedLen = 384,
  parameter int CtrLen  = 32
) (
  input logic                clk_i,
  input logic                rst_ni,

   // command interface
  input logic                ctr_drbg_cmd_enable_i,
  input logic                ctr_drbg_cmd_req_i,
  output logic               ctr_drbg_cmd_rdy_o, // ready to process the req above
  input logic [Cmd-1:0]      ctr_drbg_cmd_ccmd_i,    // current command
  input logic [StateId-1:0]  ctr_drbg_cmd_inst_id_i, // instantance id
  input logic                ctr_drbg_cmd_glast_i,   // gen cmd last beat
  input logic [SeedLen-1:0]  ctr_drbg_cmd_entropy_i, // es entropy
  input logic                ctr_drbg_cmd_entropy_fips_i, // es entropy)fips
  input logic [SeedLen-1:0]  ctr_drbg_cmd_adata_i,   // additional data
  input logic [KeyLen-1:0]   ctr_drbg_cmd_key_i,
  input logic [BlkLen-1:0]   ctr_drbg_cmd_v_i,
  input logic [CtrLen-1:0]   ctr_drbg_cmd_rc_i,
  input logic                ctr_drbg_cmd_fips_i,

  output logic               ctr_drbg_cmd_ack_o, // final ack when update process has been completed
  output logic               ctr_drbg_cmd_sts_o, // final ack status
  input logic                ctr_drbg_cmd_rdy_i, // ready to process the ack above
  output logic [Cmd-1:0]     ctr_drbg_cmd_ccmd_o,
  output logic [StateId-1:0] ctr_drbg_cmd_inst_id_o,
  output logic               ctr_drbg_cmd_glast_o,
  output logic               ctr_drbg_cmd_fips_o,
  output logic [SeedLen-1:0] ctr_drbg_cmd_adata_o,
  output logic [KeyLen-1:0]  ctr_drbg_cmd_key_o,
  output logic [BlkLen-1:0]  ctr_drbg_cmd_v_o,
  output logic [CtrLen-1:0]  ctr_drbg_cmd_rc_o,

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
  output logic [2:0]         ctr_drbg_cmd_sfifo_cmdreq_err_o,
  output logic [2:0]         ctr_drbg_cmd_sfifo_rcstage_err_o,
  output logic [2:0]         ctr_drbg_cmd_sfifo_keyvrc_err_o
);

  localparam int CmdreqFifoDepth = 1;
  localparam int CmdreqFifoWidth = KeyLen+BlkLen+CtrLen+1+2*SeedLen+1+StateId+Cmd;
  localparam int RCStageFifoDepth = 1;
  localparam int RCStageFifoWidth = KeyLen+BlkLen+StateId+CtrLen+1+SeedLen+1+Cmd;
  localparam int KeyVRCFifoDepth = 1;
  localparam int KeyVRCFifoWidth = KeyLen+BlkLen+CtrLen+1+SeedLen+1+StateId+Cmd;


  // signals
  logic [Cmd-1:0]     cmdreq_ccmd;
  logic [StateId-1:0] cmdreq_id;
  logic               cmdreq_glast;
  logic [SeedLen-1:0] cmdreq_entropy;
  logic               cmdreq_entropy_fips;
  logic [SeedLen-1:0] cmdreq_adata;
  logic [KeyLen-1:0]  cmdreq_key;
  logic [BlkLen-1:0]  cmdreq_v;
  logic [CtrLen-1:0]  cmdreq_rc;

  logic [SeedLen-1:0] prep_seed_material;
  logic [KeyLen-1:0]  prep_key;
  logic [BlkLen-1:0]  prep_v;
  logic [CtrLen-1:0]  prep_rc;
  logic               prep_gen_adata_null;
  logic [KeyLen-1:0]  rcstage_key;
  logic [BlkLen-1:0]  rcstage_v;
  logic [StateId-1:0] rcstage_id;
  logic [CtrLen-1:0]  rcstage_rc;
  logic [Cmd-1:0]     rcstage_ccmd;
  logic               rcstage_glast;
  logic [SeedLen-1:0] rcstage_adata;
  logic               rcstage_fips;
  logic               fips_modified;

  // cmdreq fifo
  logic [CmdreqFifoWidth-1:0] sfifo_cmdreq_rdata;
  logic                       sfifo_cmdreq_push;
  logic [CmdreqFifoWidth-1:0] sfifo_cmdreq_wdata;
  logic                       sfifo_cmdreq_pop;
  logic                       sfifo_cmdreq_full;
  logic                       sfifo_cmdreq_not_empty;

  // rcstage fifo
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_rdata;
  logic                        sfifo_rcstage_push;
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_wdata;
  logic                        sfifo_rcstage_pop;
  logic                        sfifo_rcstage_full;
  logic                        sfifo_rcstage_not_empty;

  // keyvrc fifo
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_rdata;
  logic                        sfifo_keyvrc_push;
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_wdata;
  logic                        sfifo_keyvrc_pop;
  logic                        sfifo_keyvrc_full;
  logic                        sfifo_keyvrc_not_empty;

  // flops
  logic                        gen_adata_null_q, gen_adata_null_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      gen_adata_null_q  <= '0;
    end else begin
      gen_adata_null_q  <= gen_adata_null_d;
    end
  end

  //--------------------------------------------
  // input request fifo for staging cmd request
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(CmdreqFifoWidth),
    .Pass(0),
    .Depth(CmdreqFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_cmdreq (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_cmd_enable_i),
    .wvalid_i       (sfifo_cmdreq_push),
    .wready_o       (),
    .wdata_i        (sfifo_cmdreq_wdata),
    .rvalid_o       (sfifo_cmdreq_not_empty),
    .rready_i       (sfifo_cmdreq_pop),
    .rdata_o        (sfifo_cmdreq_rdata),
    .full_o         (sfifo_cmdreq_full),
    .depth_o        (),
    .err_o          ()
  );

  assign fips_modified = ((ctr_drbg_cmd_ccmd_i == INS) ||
                          (ctr_drbg_cmd_ccmd_i == RES)) ? ctr_drbg_cmd_entropy_fips_i :
                         ctr_drbg_cmd_fips_i;

  assign sfifo_cmdreq_wdata = {ctr_drbg_cmd_key_i,ctr_drbg_cmd_v_i,
                               ctr_drbg_cmd_rc_i,fips_modified,
                               ctr_drbg_cmd_entropy_i,ctr_drbg_cmd_adata_i,
                               ctr_drbg_cmd_glast_i,
                               ctr_drbg_cmd_inst_id_i,ctr_drbg_cmd_ccmd_i};

  assign sfifo_cmdreq_push = ctr_drbg_cmd_enable_i && ctr_drbg_cmd_req_i;

  assign sfifo_cmdreq_pop = ctr_drbg_cmd_enable_i &&
         (upd_cmd_rdy_i || gen_adata_null_q) && sfifo_cmdreq_not_empty;

  assign {cmdreq_key,cmdreq_v,cmdreq_rc,
          cmdreq_entropy_fips,cmdreq_entropy,cmdreq_adata,
          cmdreq_glast,cmdreq_id,cmdreq_ccmd} = sfifo_cmdreq_rdata;

  assign ctr_drbg_cmd_rdy_o = !sfifo_cmdreq_full;

  assign ctr_drbg_cmd_sfifo_cmdreq_err_o =
         {(sfifo_cmdreq_push && sfifo_cmdreq_full),
          (sfifo_cmdreq_pop && !sfifo_cmdreq_not_empty),
          (sfifo_cmdreq_full && !sfifo_cmdreq_not_empty)};


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

  assign prep_gen_adata_null = (cmdreq_ccmd == GEN) && (cmdreq_adata == '0);

  assign gen_adata_null_d = ~ctr_drbg_cmd_enable_i ? '0 : prep_gen_adata_null;

  // send to the update block
  assign cmd_upd_req_o = sfifo_cmdreq_not_empty && !prep_gen_adata_null;
  assign cmd_upd_ccmd_o = cmdreq_ccmd;
  assign cmd_upd_inst_id_o = cmdreq_id;
  assign cmd_upd_pdata_o = prep_seed_material;
  assign cmd_upd_key_o = prep_key;
  assign cmd_upd_v_o = prep_v;



  //--------------------------------------------
  // fifo to stage rc and command, waiting for update block to ack
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(RCStageFifoWidth),
    .Pass(0),
    .Depth(RCStageFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_rcstage (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_cmd_enable_i),
    .wvalid_i       (sfifo_rcstage_push),
    .wready_o       (),
    .wdata_i        (sfifo_rcstage_wdata),
    .rvalid_o       (sfifo_rcstage_not_empty),
    .rready_i       (sfifo_rcstage_pop),
    .rdata_o        (sfifo_rcstage_rdata),
    .full_o         (sfifo_rcstage_full),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_rcstage_push = sfifo_cmdreq_pop;
  assign sfifo_rcstage_wdata = {prep_key,prep_v,cmdreq_id,prep_rc,cmdreq_entropy_fips,
                                cmdreq_adata,cmdreq_glast,cmdreq_ccmd};
  assign sfifo_rcstage_pop = sfifo_rcstage_not_empty && (upd_cmd_ack_i || gen_adata_null_q);
  assign {rcstage_key,rcstage_v,rcstage_id,rcstage_rc,rcstage_fips,
          rcstage_adata,rcstage_glast,rcstage_ccmd} = sfifo_rcstage_rdata;


  assign ctr_drbg_cmd_sfifo_rcstage_err_o =
         {(sfifo_rcstage_push && sfifo_rcstage_full),
          (sfifo_rcstage_pop && !sfifo_rcstage_not_empty),
          (sfifo_rcstage_full && !sfifo_rcstage_not_empty)};

  assign cmd_upd_rdy_o = sfifo_rcstage_not_empty && !sfifo_keyvrc_full;

  //--------------------------------------------
  // final cmd block processing
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(KeyVRCFifoWidth),
    .Pass(0),
    .Depth(KeyVRCFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_keyvrc (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_cmd_enable_i),
    .wvalid_i       (sfifo_keyvrc_push),
    .wready_o       (),
    .wdata_i        (sfifo_keyvrc_wdata),
    .rvalid_o       (sfifo_keyvrc_not_empty),
    .rready_i       (sfifo_keyvrc_pop),
    .rdata_o        (sfifo_keyvrc_rdata),
    .full_o         (sfifo_keyvrc_full),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_keyvrc_push = sfifo_rcstage_pop;

  // if a UNI command, reset the state values
  assign sfifo_keyvrc_wdata = (rcstage_ccmd == UNI) ?
         {{(KeyLen+BlkLen+CtrLen+1+SeedLen){1'b0}},rcstage_glast,upd_cmd_inst_id_i,upd_cmd_ccmd_i} :
         gen_adata_null_q ?
         {rcstage_key,rcstage_v,rcstage_rc,rcstage_fips,
          rcstage_adata,rcstage_glast,rcstage_id,rcstage_ccmd} :
         {upd_cmd_key_i,upd_cmd_v_i,rcstage_rc,rcstage_fips,
          rcstage_adata,rcstage_glast,upd_cmd_inst_id_i,upd_cmd_ccmd_i};

  assign sfifo_keyvrc_pop = ctr_drbg_cmd_rdy_i && sfifo_keyvrc_not_empty;
  assign {ctr_drbg_cmd_key_o,ctr_drbg_cmd_v_o,ctr_drbg_cmd_rc_o,
          ctr_drbg_cmd_fips_o,ctr_drbg_cmd_adata_o,ctr_drbg_cmd_glast_o,
          ctr_drbg_cmd_inst_id_o,ctr_drbg_cmd_ccmd_o} = sfifo_keyvrc_rdata;

  assign ctr_drbg_cmd_sfifo_keyvrc_err_o =
         {(sfifo_keyvrc_push && sfifo_keyvrc_full),
          (sfifo_keyvrc_pop && !sfifo_keyvrc_not_empty),
          (sfifo_keyvrc_full && !sfifo_keyvrc_not_empty)};

  // block ack
  assign ctr_drbg_cmd_ack_o = sfifo_keyvrc_pop;

  assign ctr_drbg_cmd_sts_o = sfifo_keyvrc_pop && (ctr_drbg_cmd_ccmd_o == UNI) &&
         ((KeyLen == '0) && (BlkLen == '0) && (CtrLen == '0));


endmodule
