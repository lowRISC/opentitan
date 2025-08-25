// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng ctr_drbg commands module
//
// Accepts all csrng commands

`include "prim_assert.sv"

module csrng_ctr_drbg_cmd import csrng_pkg::*; (
  input  logic               clk_i,
  input  logic               rst_ni,

  input  logic               enable_i,

  // command request
  input  logic               cmd_data_req_vld_i,
  output logic               cmd_data_req_rdy_o,
  input  csrng_core_data_t   cmd_data_req_i,
  input  logic [SeedLen-1:0] cmd_data_req_entropy_i,
  input  logic               cmd_data_req_entropy_fips_i,
  input  logic               cmd_data_req_glast_i,

  // command response
  output logic               cmd_data_rsp_vld_o, // final ack when update process has been completed
  input  logic               cmd_data_rsp_rdy_i,
  output csrng_core_data_t   cmd_data_rsp_o,
  output csrng_cmd_sts_e     cmd_data_rsp_status_o,
  output logic               cmd_data_rsp_glast_o,

  // update request interface
  output logic               cmd_upd_req_vld_o,
  input  logic               cmd_upd_req_rdy_i,
  output csrng_upd_data_t    cmd_upd_req_data_o,

  // update response interface
  input  logic               cmd_upd_rsp_vld_i,
  output logic               cmd_upd_rsp_rdy_o,
  input  csrng_upd_data_t    cmd_upd_rsp_data_i,

  // error status outputs
  output logic [2:0]         ctr_drbg_cmd_sfifo_cmdreq_err_o,
  output logic [2:0]         ctr_drbg_cmd_sfifo_rcstage_err_o,
  output logic [2:0]         ctr_drbg_cmd_sfifo_keyvrc_err_o
);

  localparam int CmdreqFifoWidth = CoreDataWidth + SeedLen + 1;
  localparam int RCStageFifoDepth = 1;
  localparam int RCStageFifoWidth = KeyLen+BlkLen+InstIdWidth+CtrLen+1+SeedLen+1+CmdWidth;
  localparam int KeyVRCFifoDepth = 1;
  localparam int KeyVRCFifoWidth = KeyLen+BlkLen+CtrLen+1+SeedLen+1+InstIdWidth+CmdWidth;


  // signals
  csrng_core_data_t   cmdreq_data;
  logic [SeedLen-1:0] cmdreq_entropy;
  logic               cmdreq_glast;

  

  logic [SeedLen-1:0] prep_seed_material;
  logic [KeyLen-1:0]  prep_key;
  logic [BlkLen-1:0]  prep_v;
  logic [CtrLen-1:0]  prep_rc;
  logic               prep_gen_adata_null;
  logic [KeyLen-1:0]  rcstage_key;
  logic [BlkLen-1:0]  rcstage_v;
  logic [InstIdWidth-1:0] rcstage_id;
  logic [CtrLen-1:0]  rcstage_rc;
  logic [CmdWidth-1:0]rcstage_ccmd;
  logic               rcstage_glast;
  logic [SeedLen-1:0] rcstage_adata;
  logic               rcstage_fips;
  logic               fips_muxed;

  // cmdreq fifo
  logic                       sfifo_cmdreq_wvld;
  logic                       sfifo_cmdreq_wrdy;
  logic [CmdreqFifoWidth-1:0] sfifo_cmdreq_wdata;
  logic                       sfifo_cmdreq_rvld;
  logic                       sfifo_cmdreq_rrdy;
  logic [CmdreqFifoWidth-1:0] sfifo_cmdreq_rdata;
  logic                       sfifo_cmdreq_full;
  
  // rcstage fifo
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_rdata;
  logic                        sfifo_rcstage_wvld;
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_wdata;
  logic                        sfifo_rcstage_rrdy;
  logic                        sfifo_rcstage_full;
  logic                        sfifo_rcstage_rvld;

  // keyvrc fifo
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_rdata;
  logic                        sfifo_keyvrc_wvld;
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_wdata;
  logic                        sfifo_keyvrc_rrdy;
  logic                        sfifo_keyvrc_full;
  logic                        sfifo_keyvrc_rvld;

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

  csrng_core_data_t cmd_data_req_fifo;

  prim_fifo_sync #(
    .Width(CmdreqFifoWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_cmdreq (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!enable_i),
    .wvalid_i       (sfifo_cmdreq_wvld),
    .wready_o       (sfifo_cmdreq_wrdy),
    .wdata_i        (sfifo_cmdreq_wdata),
    .rvalid_o       (sfifo_cmdreq_rvld),
    .rready_i       (sfifo_cmdreq_rrdy),
    .rdata_o        (sfifo_cmdreq_rdata),
    .full_o         (sfifo_cmdreq_full),
    .depth_o        (),
    .err_o          ()
  );

  always_comb begin
    cmd_data_req_fifo = cmd_data_req_i;
    // Insert the FIPS info from entropy source on instantiate and reseed commands.
    // Else, keep the existing info (from state db).
    cmd_data_req_fifo.fips = ((cmd_data_req_i.cmd == INS) || (cmd_data_req_i.cmd == RES)) ? 
                               cmd_data_req_entropy_fips_i : cmd_data_req_i.fips;
  end

  assign sfifo_cmdreq_wdata = {cmd_data_req_glast_i,
                               cmd_data_req_entropy_i,
                               cmd_data_req_fifo};

  assign {cmdreq_glast,
          cmdreq_entropy,
          cmdreq_data}   = sfifo_cmdreq_rdata;

  assign sfifo_cmdreq_wvld = enable_i && cmd_data_req_vld_i;
  assign sfifo_cmdreq_rrdy = enable_i && (cmd_upd_req_rdy_i || gen_adata_null_q) &&
                             sfifo_cmdreq_rvld;
  assign cmd_data_req_rdy_o = sfifo_cmdreq_wrdy;

  assign ctr_drbg_cmd_sfifo_cmdreq_err_o =
         {(sfifo_cmdreq_wvld && sfifo_cmdreq_full),
          (sfifo_cmdreq_rrdy && !sfifo_cmdreq_rvld),
          (sfifo_cmdreq_full && !sfifo_cmdreq_rvld)};

  //--------------------------------------------
  // prepare values for update step
  //--------------------------------------------

  assign prep_seed_material =
         (cmdreq_data.cmd == INS) ? (cmdreq_entropy ^ cmdreq_data.pdata) :
         (cmdreq_data.cmd == RES) ? (cmdreq_entropy ^ cmdreq_data.pdata) :
         (cmdreq_data.cmd == GEN) ? cmdreq_data.pdata :
         (cmdreq_data.cmd == UPD) ? cmdreq_data.pdata :
         '0;

  assign prep_key =
         (cmdreq_data.cmd == INS) ? {KeyLen{1'b0}} :
         (cmdreq_data.cmd == RES) ? cmdreq_data.key :
         (cmdreq_data.cmd == GEN) ? cmdreq_data.key :
         (cmdreq_data.cmd == UPD) ? cmdreq_data.key :
         '0;

  assign prep_v =
         (cmdreq_data.cmd == INS) ? {BlkLen{1'b0}} :
         (cmdreq_data.cmd == RES) ? cmdreq_data.v :
         (cmdreq_data.cmd == GEN) ? cmdreq_data.v :
         (cmdreq_data.cmd == UPD) ? cmdreq_data.v :
         '0;

  assign prep_rc =
         (cmdreq_data.cmd == INS) ? {{(CtrLen-1){1'b0}},1'b0} :
         (cmdreq_data.cmd == RES) ? {{(CtrLen-1){1'b0}},1'b0} :
         (cmdreq_data.cmd == GEN) ? cmdreq_data.rs_ctr :
         (cmdreq_data.cmd == UPD) ? cmdreq_data.rs_ctr :
         '0;

  assign prep_gen_adata_null = (cmdreq_data.cmd == GEN) && (cmdreq_data.pdata == '0);

  assign gen_adata_null_d = !enable_i ? '0 : prep_gen_adata_null;

  // send to the update block
  assign cmd_upd_req_vld_o = sfifo_cmdreq_rvld && !prep_gen_adata_null;
  assign cmd_upd_req_data_o = '{
    inst_id: cmdreq_data.inst_id,
    cmd:     cmdreq_data.cmd,
    key:     prep_key,
    v:       prep_v,
    pdata:   prep_seed_material
  };

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
    .clr_i          (!enable_i),
    .wvalid_i       (sfifo_rcstage_wvld),
    .wready_o       (),
    .wdata_i        (sfifo_rcstage_wdata),
    .rvalid_o       (sfifo_rcstage_rvld),
    .rready_i       (sfifo_rcstage_rrdy),
    .rdata_o        (sfifo_rcstage_rdata),
    .full_o         (sfifo_rcstage_full),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_rcstage_wvld = sfifo_cmdreq_rrdy;
  assign sfifo_rcstage_wdata = {prep_key,prep_v,cmdreq_data.inst_id,prep_rc,cmdreq_data.fips,
                                cmdreq_data.pdata,cmdreq_glast,cmdreq_data.cmd};
  assign sfifo_rcstage_rrdy = sfifo_rcstage_rvld && (cmd_upd_rsp_vld_i || gen_adata_null_q);
  assign {rcstage_key,rcstage_v,rcstage_id,rcstage_rc,rcstage_fips,
          rcstage_adata,rcstage_glast,rcstage_ccmd} = sfifo_rcstage_rdata;


  assign ctr_drbg_cmd_sfifo_rcstage_err_o =
         {(sfifo_rcstage_wvld && sfifo_rcstage_full),
          (sfifo_rcstage_rrdy && !sfifo_rcstage_rvld),
          (sfifo_rcstage_full && !sfifo_rcstage_rvld)};

  assign cmd_upd_rsp_rdy_o = sfifo_rcstage_rvld && !sfifo_keyvrc_full;

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
    .clr_i          (!enable_i),
    .wvalid_i       (sfifo_keyvrc_wvld),
    .wready_o       (),
    .wdata_i        (sfifo_keyvrc_wdata),
    .rvalid_o       (sfifo_keyvrc_rvld),
    .rready_i       (sfifo_keyvrc_rrdy),
    .rdata_o        (sfifo_keyvrc_rdata),
    .full_o         (sfifo_keyvrc_full),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_keyvrc_wvld = sfifo_rcstage_rrdy;

  // if a UNI command, reset the state values
  assign sfifo_keyvrc_wdata = (rcstage_ccmd == UNI) ?
         {{(KeyLen+BlkLen+CtrLen+1+SeedLen){1'b0}},rcstage_glast,cmd_upd_rsp_data_i.inst_id,cmd_upd_rsp_data_i.cmd} :
         gen_adata_null_q ?
         {rcstage_key,rcstage_v,rcstage_rc,rcstage_fips,
          rcstage_adata,rcstage_glast,rcstage_id,rcstage_ccmd} :
         {cmd_upd_rsp_data_i.key,cmd_upd_rsp_data_i.v,rcstage_rc,rcstage_fips,
          rcstage_adata,rcstage_glast,cmd_upd_rsp_data_i.inst_id,cmd_upd_rsp_data_i.cmd};

  assign sfifo_keyvrc_rrdy = cmd_data_rsp_rdy_i && sfifo_keyvrc_rvld;

  // cmd response output assignments
  assign {cmd_data_rsp_o.key,
          cmd_data_rsp_o.v,
          cmd_data_rsp_o.rs_ctr,
          cmd_data_rsp_o.fips,
          cmd_data_rsp_o.pdata,
          cmd_data_rsp_glast_o,
          cmd_data_rsp_o.inst_id,
          cmd_data_rsp_o.cmd} = sfifo_keyvrc_rdata;

  assign cmd_data_rsp_vld_o = sfifo_keyvrc_rrdy;
  assign cmd_data_rsp_status_o = CMD_STS_SUCCESS;

  assign ctr_drbg_cmd_sfifo_keyvrc_err_o =
         {(sfifo_keyvrc_wvld && sfifo_keyvrc_full),
          (sfifo_keyvrc_rrdy && !sfifo_keyvrc_rvld),
          (sfifo_keyvrc_full && !sfifo_keyvrc_rvld)};

endmodule
