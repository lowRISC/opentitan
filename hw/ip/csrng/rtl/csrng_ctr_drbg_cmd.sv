// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng ctr_drbg commands module
//
// Decodes the command field of an operation, injects entropy to pdata if required, and performs
// the initial call to update() for all commands where this is required and pdata != 0.

`include "prim_assert.sv"

module csrng_ctr_drbg_cmd import csrng_pkg::*; (
  input  logic               clk_i,
  input  logic               rst_ni,

  // Global enable
  input  logic               enable_i,

  // Command interface request, arbitrated from command stages
  input  logic               req_vld_i,
  output logic               req_rdy_o,
  input  csrng_core_data_t   req_data_i,
  input  logic [SeedLen-1:0] req_entropy_i,
  input  logic               req_entropy_fips_i,
  input  logic               req_glast_i,

  // Command interface response to update unit or state db
  output logic               rsp_vld_o,
  input  logic               rsp_rdy_i,
  output csrng_core_data_t   rsp_data_o,
  output logic               rsp_glast_o,

  // Update interface request
  output logic               update_req_vld_o,
  input  logic               update_req_rdy_i,
  output csrng_upd_data_t    update_req_data_o,

  // Update interface response
  input  logic               update_rsp_vld_i,
  output logic               update_rsp_rdy_o,
  input  csrng_upd_data_t    update_rsp_data_i,

  // Error status outputs
  output logic         [2:0] fifo_cmdreq_err_o,
  output logic         [2:0] fifo_rcstage_err_o,
  output logic         [2:0] fifo_keyvrc_err_o
);

  localparam int CmdreqFifoWidth  = CoreDataWidth + SeedLen + 1;
  localparam int RCStageFifoWidth = CoreDataWidth + 1;
  localparam int KeyVRCFifoWidth  = CoreDataWidth + 1;

  // signals
  csrng_core_data_t   cmdreq_data;
  logic [SeedLen-1:0] cmdreq_entropy;
  logic               cmdreq_glast;

  csrng_core_data_t   rcstage_data;
  logic               rcstage_glast;

  csrng_core_data_t   keyvrc_data;
  logic               keyvrc_glast;

  logic [SeedLen-1:0] prep_seed_material;
  logic [KeyLen-1:0]  prep_key;
  logic [BlkLen-1:0]  prep_v;
  logic [CtrLen-1:0]  prep_rc;
  logic               prep_gen_adata_null;

  // cmdreq fifo
  logic                        sfifo_cmdreq_wvld;
  logic                        sfifo_cmdreq_wrdy;
  logic  [CmdreqFifoWidth-1:0] sfifo_cmdreq_wdata;
  logic                        sfifo_cmdreq_rvld;
  logic                        sfifo_cmdreq_rrdy;
  logic  [CmdreqFifoWidth-1:0] sfifo_cmdreq_rdata;

  // rcstage fifo
  logic                        sfifo_rcstage_wvld;
  logic                        sfifo_rcstage_wrdy;
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_wdata;
  logic                        sfifo_rcstage_rvld;
  logic                        sfifo_rcstage_rrdy;
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_rdata;

  // keyvrc fifo
  logic                        sfifo_keyvrc_wvld;
  logic                        sfifo_keyvrc_wrdy;
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_wdata;
  logic                        sfifo_keyvrc_rvld;
  logic                        sfifo_keyvrc_rrdy;
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_rdata;

  // flops
  logic                        gen_adata_null_q, gen_adata_null_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      gen_adata_null_q <= '0;
    end else begin
      gen_adata_null_q <= gen_adata_null_d;
    end
  end

  //--------------------------------------------
  // input request fifo for staging cmd request
  //--------------------------------------------

  csrng_core_data_t req_data_fifo;

  prim_fifo_sync #(
    .Width(CmdreqFifoWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_cmdreq (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_cmdreq_wvld),
    .wready_o(sfifo_cmdreq_wrdy),
    .wdata_i (sfifo_cmdreq_wdata),
    .rvalid_o(sfifo_cmdreq_rvld),
    .rready_i(sfifo_cmdreq_rrdy),
    .rdata_o (sfifo_cmdreq_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  always_comb begin
    req_data_fifo = req_data_i;
    // Insert the FIPS info from entropy source on instantiate and reseed commands.
    // Else, keep the existing info (from state db).
    req_data_fifo.fips = ((req_data_i.cmd == INS) || (req_data_i.cmd == RES)) ?
                           req_entropy_fips_i : req_data_i.fips;
  end

  assign sfifo_cmdreq_wdata = {req_glast_i,
                               req_entropy_i,
                               req_data_fifo};

  assign {cmdreq_glast,
          cmdreq_entropy,
          cmdreq_data}   = sfifo_cmdreq_rdata;

  assign sfifo_cmdreq_wvld = enable_i && req_vld_i;
  assign sfifo_cmdreq_rrdy = enable_i && (update_req_rdy_i || gen_adata_null_q) &&
                             sfifo_cmdreq_rvld;
  assign req_rdy_o = sfifo_cmdreq_wrdy;

  assign fifo_cmdreq_err_o =
         {( sfifo_cmdreq_wvld && !sfifo_cmdreq_wrdy),
          ( sfifo_cmdreq_rrdy && !sfifo_cmdreq_rvld),
          (!sfifo_cmdreq_wrdy && !sfifo_cmdreq_rvld)};

  //--------------------------------------------
  // Prepare (mostly: mux) values for update step
  //--------------------------------------------

  assign prep_seed_material =
         (cmdreq_data.cmd == INS) ? (cmdreq_entropy ^ cmdreq_data.pdata) :
         (cmdreq_data.cmd == RES) ? (cmdreq_entropy ^ cmdreq_data.pdata) :
         (cmdreq_data.cmd == GEN) ? cmdreq_data.pdata :
         (cmdreq_data.cmd == UPD) ? cmdreq_data.pdata :
         '0;

  assign prep_key =
         (cmdreq_data.cmd == INS) ? '0 :
         (cmdreq_data.cmd == RES) ? cmdreq_data.key :
         (cmdreq_data.cmd == GEN) ? cmdreq_data.key :
         (cmdreq_data.cmd == UPD) ? cmdreq_data.key :
         '0;

  assign prep_v =
         (cmdreq_data.cmd == INS) ? '0 :
         (cmdreq_data.cmd == RES) ? cmdreq_data.v :
         (cmdreq_data.cmd == GEN) ? cmdreq_data.v :
         (cmdreq_data.cmd == UPD) ? cmdreq_data.v :
         '0;

  assign prep_rc =
         (cmdreq_data.cmd == INS) ? '0 :
         (cmdreq_data.cmd == RES) ? '0 :
         (cmdreq_data.cmd == GEN) ? cmdreq_data.rs_ctr :
         (cmdreq_data.cmd == UPD) ? cmdreq_data.rs_ctr :
         '0;

  assign prep_gen_adata_null = (cmdreq_data.cmd == GEN) && (cmdreq_data.pdata == '0);

  assign gen_adata_null_d = !enable_i ? '0 : prep_gen_adata_null;

  // send to the update block
  assign update_req_vld_o = sfifo_cmdreq_rvld && !prep_gen_adata_null;
  assign update_req_data_o = '{
    inst_id: cmdreq_data.inst_id,
    cmd:     cmdreq_data.cmd,
    key:     prep_key,
    v:       prep_v,
    pdata:   prep_seed_material
  };

  //--------------------------------------------
  // fifo to stage rc and command, waiting for update block to ack
  //--------------------------------------------

  csrng_core_data_t rcstage_core_data_fifo;

  prim_fifo_sync #(
    .Width(RCStageFifoWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_rcstage (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_rcstage_wvld),
    .wready_o(sfifo_rcstage_wrdy),
    .wdata_i (sfifo_rcstage_wdata),
    .rvalid_o(sfifo_rcstage_rvld),
    .rready_i(sfifo_rcstage_rrdy),
    .rdata_o (sfifo_rcstage_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  always_comb begin
    rcstage_core_data_fifo = cmdreq_data;
    rcstage_core_data_fifo.key    = prep_key;
    rcstage_core_data_fifo.v      = prep_v;
    rcstage_core_data_fifo.rs_ctr = prep_rc;
  end

  assign sfifo_rcstage_wdata = {cmdreq_glast,
                                rcstage_core_data_fifo};

  assign {rcstage_glast,
          rcstage_data} = sfifo_rcstage_rdata;

  assign sfifo_rcstage_wvld = sfifo_cmdreq_rrdy;
  assign sfifo_rcstage_rrdy = sfifo_rcstage_rvld && (update_rsp_vld_i || gen_adata_null_q);

  assign update_rsp_rdy_o = sfifo_rcstage_rvld && sfifo_keyvrc_wrdy;

  assign fifo_rcstage_err_o =
         {( sfifo_rcstage_wvld && !sfifo_rcstage_wrdy),
          ( sfifo_rcstage_rrdy && !sfifo_rcstage_rvld),
          (!sfifo_rcstage_wrdy && !sfifo_rcstage_rvld)};

  //--------------------------------------------
  // final cmd block processing
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(KeyVRCFifoWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_keyvrc (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_keyvrc_wvld),
    .wready_o(sfifo_keyvrc_wrdy),
    .wdata_i (sfifo_keyvrc_wdata),
    .rvalid_o(sfifo_keyvrc_rvld),
    .rready_i(sfifo_keyvrc_rrdy),
    .rdata_o (sfifo_keyvrc_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  assign sfifo_keyvrc_wvld = sfifo_rcstage_rrdy;

  always_comb begin
    keyvrc_data  = rcstage_data;
    keyvrc_glast = rcstage_glast;
    if (rcstage_data.cmd == UNI) begin
      // Zeroize everything but inst_id and cmd (?)
      keyvrc_data = '{default: '0};
      keyvrc_data.inst_id = rcstage_data.inst_id;
      keyvrc_data.cmd     = rcstage_data.cmd;
    end else if (!gen_adata_null_q) begin
      // Update key and v with values from the update unit if
      // non-zero pdata were provided
      keyvrc_data.key     = update_rsp_data_i.key;
      keyvrc_data.v       = update_rsp_data_i.v;
      keyvrc_data.inst_id = update_rsp_data_i.inst_id;
      keyvrc_data.cmd     = update_rsp_data_i.cmd;
    end
  end

  assign sfifo_keyvrc_wdata = {keyvrc_glast,
                               keyvrc_data};

  assign sfifo_keyvrc_rrdy = rsp_rdy_i && sfifo_keyvrc_rvld;

  // cmd response output assignments
  assign {rsp_glast_o,
          rsp_data_o} = sfifo_keyvrc_rdata;

  assign rsp_vld_o = sfifo_keyvrc_rrdy;

  assign fifo_keyvrc_err_o =
         {( sfifo_keyvrc_wvld && !sfifo_keyvrc_wrdy),
          ( sfifo_keyvrc_rrdy && !sfifo_keyvrc_rvld),
          (!sfifo_keyvrc_wrdy && !sfifo_keyvrc_rvld)};

  // Unused signals
  logic [SeedLen-1:0] unused_upd_rsp_pdata;
  assign unused_upd_rsp_pdata = update_rsp_data_i.pdata;

endmodule
