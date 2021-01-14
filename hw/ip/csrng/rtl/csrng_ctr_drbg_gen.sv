// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng ctr_drbg generate module
//
// This module will process the second half of the generate function.
// It takes in the key, v, and reseed counter values processed by the
// ctr_drbg cmd module.

module csrng_ctr_drbg_gen import csrng_pkg::*; #(
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
  input logic                ctr_drbg_gen_enable_i,
  input logic                ctr_drbg_gen_req_i,
  output logic               ctr_drbg_gen_rdy_o, // ready to process the req above
  input logic [Cmd-1:0]      ctr_drbg_gen_ccmd_i,    // current command
  input logic [StateId-1:0]  ctr_drbg_gen_inst_id_i, // instantance id
  input logic                ctr_drbg_gen_fips_i,    // fips
  input logic [SeedLen-1:0]  ctr_drbg_gen_adata_i,   // additional data
  input logic [KeyLen-1:0]   ctr_drbg_gen_key_i,
  input logic [BlkLen-1:0]   ctr_drbg_gen_v_i,
  input logic [CtrLen-1:0]   ctr_drbg_gen_rc_i,

  output logic               ctr_drbg_gen_ack_o, // final ack when update process has been completed
  output logic               ctr_drbg_gen_sts_o, // final ack status
  input logic                ctr_drbg_gen_rdy_i, // ready to process the ack above
  output logic [Cmd-1:0]     ctr_drbg_gen_ccmd_o,
  output logic [StateId-1:0] ctr_drbg_gen_inst_id_o,
  output logic [KeyLen-1:0]  ctr_drbg_gen_key_o,
  output logic [BlkLen-1:0]  ctr_drbg_gen_v_o,
  output logic [CtrLen-1:0]  ctr_drbg_gen_rc_o,
  output logic [BlkLen-1:0]  ctr_drbg_gen_bits_o,
  output logic               ctr_drbg_gen_fips_o,
  // update interface
  output logic               gen_upd_req_o,
  input logic                upd_gen_rdy_i,
  output logic [Cmd-1:0]     gen_upd_ccmd_o,
  output logic [StateId-1:0] gen_upd_inst_id_o,
  output logic [SeedLen-1:0] gen_upd_pdata_o,
  output logic [KeyLen-1:0]  gen_upd_key_o,
  output logic [BlkLen-1:0]  gen_upd_v_o,

  input logic                upd_gen_ack_i,
  output logic               gen_upd_rdy_o,
  input logic [Cmd-1:0]      upd_gen_ccmd_i,
  input logic [StateId-1:0]  upd_gen_inst_id_i,
  input logic [KeyLen-1:0]   upd_gen_key_i,
  input logic [BlkLen-1:0]   upd_gen_v_i,
  // block encrypt interface
  output logic               block_encrypt_req_o,
  input logic                block_encrypt_rdy_i,
  output logic [Cmd-1:0]     block_encrypt_ccmd_o,
  output logic [StateId-1:0] block_encrypt_inst_id_o,
  output logic [KeyLen-1:0]  block_encrypt_key_o,
  output logic [BlkLen-1:0]  block_encrypt_v_o,
  input logic                block_encrypt_ack_i,
  output logic               block_encrypt_rdy_o,
  input logic [Cmd-1:0]      block_encrypt_ccmd_i,
  input logic [StateId-1:0]  block_encrypt_inst_id_i,
  input logic [BlkLen-1:0]   block_encrypt_v_i,
  // misc
  output logic [2:0]         ctr_drbg_gen_sfifo_gbencack_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_grcstage_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_ggenreq_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_gadstage_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_ggenbits_err_o
);

  localparam int GenreqFifoDepth = 1;
  localparam int GenreqFifoWidth = KeyLen+BlkLen+CtrLen+1+SeedLen+StateId+Cmd;
  localparam int BlkEncAckFifoDepth = 1;
  localparam int BlkEncAckFifoWidth = BlkLen+StateId+Cmd;
  localparam int AdstageFifoDepth = 1;
  localparam int AdstageFifoWidth = KeyLen+BlkLen+CtrLen+1+SeedLen;
  localparam int RCStageFifoDepth = 1;
  localparam int RCStageFifoWidth = BlkLen+CtrLen+1;
  localparam int GenbitsFifoDepth = 1;
  localparam int GenbitsFifoWidth = 1+BlkLen+KeyLen+BlkLen+CtrLen+StateId+Cmd;

  // signals
  logic [Cmd-1:0]     genreq_ccmd;
  logic [StateId-1:0] genreq_id;
  logic [SeedLen-1:0] genreq_adata;
  logic               genreq_fips;
  logic [KeyLen-1:0]  genreq_key;
  logic [BlkLen-1:0]  genreq_v;
  logic [CtrLen-1:0]  genreq_rc;

  logic [KeyLen-1:0]  adstage_key;
  logic [BlkLen-1:0]  adstage_v;
  logic [CtrLen-1:0]  adstage_rc;
  logic               adstage_fips;
  logic [SeedLen-1:0] adstage_adata;

  logic [BlkLen-1:0]  rcstage_bits;
  logic [CtrLen-1:0]  rcstage_rc;
  logic               rcstage_fips;
  logic [CtrLen-1:0]  rcstage_rc_plus1;

  logic [Cmd-1:0]     genreq_ccmd_modified;
  logic [Cmd-1:0]     bencack_ccmd_modified;

  // cmdreq fifo
  // logic [$clog2(CmdreqFifoDepth):0] sfifo_cmdreq_depth;
  logic [GenreqFifoWidth-1:0] sfifo_genreq_rdata;
  logic                       sfifo_genreq_push;
  logic [GenreqFifoWidth-1:0] sfifo_genreq_wdata;
  logic                       sfifo_genreq_pop;
  logic                       sfifo_genreq_not_full;
  logic                       sfifo_genreq_not_empty;

  // adstage fifo
  logic [AdstageFifoWidth-1:0] sfifo_adstage_rdata;
  logic                        sfifo_adstage_push;
  logic [AdstageFifoWidth-1:0] sfifo_adstage_wdata;
  logic                        sfifo_adstage_pop;
  logic                        sfifo_adstage_not_full;
  logic                        sfifo_adstage_not_empty;
  // blk_encrypt_ack fifo
  logic [BlkEncAckFifoWidth-1:0] sfifo_bencack_rdata;
  logic                       sfifo_bencack_push;
  logic [BlkEncAckFifoWidth-1:0] sfifo_bencack_wdata;
  logic                       sfifo_bencack_pop;
  logic                       sfifo_bencack_not_full;
  logic                       sfifo_bencack_not_empty;
  // breakout
  logic [Cmd-1:0]             sfifo_bencack_ccmd;
  logic [StateId-1:0]         sfifo_bencack_inst_id;
  logic [BlkLen-1:0]          sfifo_bencack_bits;

  // rcstage fifo
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_rdata;
  logic                        sfifo_rcstage_push;
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_wdata;
  logic                        sfifo_rcstage_pop;
  logic                        sfifo_rcstage_not_full;
  logic                        sfifo_rcstage_not_empty;

  // genbits fifo
  logic [GenbitsFifoWidth-1:0] sfifo_genbits_rdata;
  logic                        sfifo_genbits_push;
  logic [GenbitsFifoWidth-1:0] sfifo_genbits_wdata;
  logic                        sfifo_genbits_pop;
  logic                        sfifo_genbits_not_full;
  logic                        sfifo_genbits_not_empty;

  logic [CtrLen-1:0]           v_inc;
  logic [BlkLen-1:0]           v_first;
  logic [BlkLen-1:0]           v_sized;
  logic                        v_ctr_load;
  logic                        v_ctr_inc;
  logic                        interate_ctr_done;
  logic                        interate_ctr_inc;

  // flops
  logic [CtrLen-1:0]           v_ctr_q, v_ctr_d;
  logic [1:0]                  interate_ctr_q, interate_ctr_d;

  // Encoding generated with ./sparse-fsm-encode.py -d 3 -m 2 -n 4 -s 352244715
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: --
  // 4: |||||||||||||||||||| (100.00%)
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 4
  //
  localparam int StateWidth = 4;
  typedef enum logic [StateWidth-1:0] {
    ReqIdle = 4'b1010,
    ReqSend = 4'b0101
} state_e;

  state_e state_d, state_q;

  logic [StateWidth-1:0] state_raw_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(ReqIdle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d ),
    .q_o ( state_raw_q )
  );

  assign state_q = state_e'(state_raw_q);

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      v_ctr_q            <= '0;
      interate_ctr_q     <= '0;
    end else begin
      v_ctr_q            <= v_ctr_d;
      interate_ctr_q     <= interate_ctr_d;
    end // else: !if(!rst_ni)



  //--------------------------------------------
  // input request fifo for staging gen request
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(GenreqFifoWidth),
    .Pass(0),
    .Depth(GenreqFifoDepth)
  ) u_prim_fifo_sync_genreq (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_gen_enable_i),
    .wvalid_i       (sfifo_genreq_push),
    .wready_o       (sfifo_genreq_not_full),
    .wdata_i        (sfifo_genreq_wdata),
    .rvalid_o       (sfifo_genreq_not_empty),
    .rready_i       (sfifo_genreq_pop),
    .rdata_o        (sfifo_genreq_rdata),
    .depth_o        ()
  );

  assign genreq_ccmd_modified = (ctr_drbg_gen_ccmd_i == GEN) ? GENB : INV;

  assign sfifo_genreq_wdata = {ctr_drbg_gen_key_i,ctr_drbg_gen_v_i,ctr_drbg_gen_rc_i,
                               ctr_drbg_gen_fips_i,ctr_drbg_gen_adata_i,
                               ctr_drbg_gen_inst_id_i,genreq_ccmd_modified};

  assign sfifo_genreq_push = ctr_drbg_gen_enable_i && ctr_drbg_gen_req_i;

  assign {genreq_key,genreq_v,genreq_rc,
          genreq_fips,genreq_adata,
          genreq_id,genreq_ccmd} = sfifo_genreq_rdata;

  assign ctr_drbg_gen_rdy_o = sfifo_genreq_not_full;

  assign ctr_drbg_gen_sfifo_ggenreq_err_o =
         {(sfifo_genreq_push && !sfifo_genreq_not_full),
          (sfifo_genreq_pop && !sfifo_genreq_not_empty),
          (!sfifo_genreq_not_full && !sfifo_genreq_not_empty)};



  //--------------------------------------------
  // prepare value for block_encrypt step
  //--------------------------------------------

  if (CtrLen < BlkLen) begin : gen_ctrlen_sm
    // for ctr_len < blocklen
    assign v_inc = genreq_v[CtrLen-1:0] + 1;
    assign v_first = {genreq_v[BlkLen-1:CtrLen],v_inc};
  end else begin : g_ctrlen_lg
    assign v_first = genreq_v + 1;
  end

  assign v_ctr_d = v_ctr_load ? v_first[CtrLen-1:0] :
                   v_ctr_inc  ? (v_ctr_q + 1) :
                   v_ctr_q;

  assign v_sized = {v_first[BlkLen-1:CtrLen],v_ctr_q};

  // interation counter
  assign interate_ctr_d =
         interate_ctr_done ? '0 :
         interate_ctr_inc ? (interate_ctr_q + 1) :
         interate_ctr_q;

  // Supporting only 128b requests
  assign interate_ctr_done = (interate_ctr_q >= (BlkLen/BlkLen));

  //--------------------------------------------
  // state machine to send values to block_encrypt
  //--------------------------------------------

  assign block_encrypt_ccmd_o = genreq_ccmd;
  assign block_encrypt_inst_id_o = genreq_id;
  assign block_encrypt_key_o = genreq_key;
  assign block_encrypt_v_o = v_sized;

  always_comb begin
    state_d = state_q;
    v_ctr_load = 1'b0;
    v_ctr_inc  = 1'b0;
    interate_ctr_inc  = 1'b0;
    sfifo_adstage_push = 1'b0;
    block_encrypt_req_o = 1'b0;
    sfifo_genreq_pop = 1'b0;
    unique case (state_q)
      // ReqIdle: increment v this cycle, push in next
      ReqIdle:
        if (sfifo_genreq_not_empty && sfifo_adstage_not_full) begin
          v_ctr_load = 1'b1;
          sfifo_adstage_push = 1'b1;
          state_d = ReqSend;
        end
      ReqSend:
        if (!interate_ctr_done) begin
          block_encrypt_req_o = 1'b1;
          if (block_encrypt_rdy_i) begin
            v_ctr_inc  = 1'b1;
            interate_ctr_inc  = 1'b1;
          end
        end else begin
          sfifo_genreq_pop = 1'b1;
          state_d = ReqIdle;
        end
      default: state_d = ReqIdle;
    endcase
  end


  //--------------------------------------------
  // fifo to stage key, v, rc, and adata, waiting for update block to ack
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(AdstageFifoWidth),
    .Pass(0),
    .Depth(AdstageFifoDepth)
  ) u_prim_fifo_sync_adstage (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_gen_enable_i),
    .wvalid_i       (sfifo_adstage_push),
    .wready_o       (sfifo_adstage_not_full),
    .wdata_i        (sfifo_adstage_wdata),
    .rvalid_o       (sfifo_adstage_not_empty),
    .rready_i       (sfifo_adstage_pop),
    .rdata_o        (sfifo_adstage_rdata),
    .depth_o        ()
  );

//  assign sfifo_adstage_push = sfifo_genreq_pop;
  assign sfifo_adstage_wdata = {genreq_key,genreq_v,genreq_rc,genreq_fips,genreq_adata};
  assign sfifo_adstage_pop = sfifo_adstage_not_empty && sfifo_bencack_pop;
  assign {adstage_key,adstage_v,adstage_rc,adstage_fips,adstage_adata} = sfifo_adstage_rdata;

  assign ctr_drbg_gen_sfifo_gadstage_err_o =
         {(sfifo_adstage_push && !sfifo_adstage_not_full),
          (sfifo_adstage_pop && !sfifo_adstage_not_empty),
          (!sfifo_adstage_not_full && !sfifo_adstage_not_empty)};



  //--------------------------------------------
  // block_encrypt response fifo from block encrypt
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(BlkEncAckFifoWidth),
    .Pass(0),
    .Depth(BlkEncAckFifoDepth)
  ) u_prim_fifo_sync_bencack (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .clr_i    (!ctr_drbg_gen_enable_i),
    .wvalid_i (sfifo_bencack_push),
    .wready_o (sfifo_bencack_not_full),
    .wdata_i  (sfifo_bencack_wdata),
    .rvalid_o (sfifo_bencack_not_empty),
    .rready_i (sfifo_bencack_pop),
    .rdata_o  (sfifo_bencack_rdata),
    .depth_o  ()
  );

  assign bencack_ccmd_modified = (block_encrypt_ccmd_i == GENB) ? GENU : INV;

  assign sfifo_bencack_push = sfifo_bencack_not_full && block_encrypt_ack_i;
  assign sfifo_bencack_wdata = {block_encrypt_v_i,block_encrypt_inst_id_i,bencack_ccmd_modified};
  assign block_encrypt_rdy_o = sfifo_bencack_not_full;

  assign sfifo_bencack_pop = sfifo_rcstage_not_full && sfifo_bencack_not_empty && upd_gen_rdy_i;

  assign {sfifo_bencack_bits,sfifo_bencack_inst_id,sfifo_bencack_ccmd} = sfifo_bencack_rdata;

  assign ctr_drbg_gen_sfifo_gbencack_err_o =
         {(sfifo_bencack_push && !sfifo_bencack_not_full),
          (sfifo_bencack_pop && !sfifo_bencack_not_empty),
          (!sfifo_bencack_not_full && !sfifo_bencack_not_empty)};


  //--------------------------------------------
  // prepare values for update step
  //--------------------------------------------

  // send to the update block
  assign gen_upd_req_o = sfifo_bencack_not_empty;
  assign gen_upd_ccmd_o = sfifo_bencack_ccmd;
  assign gen_upd_inst_id_o = sfifo_bencack_inst_id;
  assign gen_upd_pdata_o = adstage_adata;
  assign gen_upd_key_o = adstage_key;
  assign gen_upd_v_o = adstage_v;



  //--------------------------------------------
  // fifo to stage rc, waiting for update block to ack
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(RCStageFifoWidth),
    .Pass(0),
    .Depth(RCStageFifoDepth)
  ) u_prim_fifo_sync_rcstage (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_gen_enable_i),
    .wvalid_i       (sfifo_rcstage_push),
    .wready_o       (sfifo_rcstage_not_full),
    .wdata_i        (sfifo_rcstage_wdata),
    .rvalid_o       (sfifo_rcstage_not_empty),
    .rready_i       (sfifo_rcstage_pop),
    .rdata_o        (sfifo_rcstage_rdata),
    .depth_o        ()
  );

  assign sfifo_rcstage_push = sfifo_adstage_pop;
  assign sfifo_rcstage_wdata = {sfifo_bencack_bits,adstage_rc,adstage_fips};
  assign sfifo_rcstage_pop = sfifo_rcstage_not_empty && upd_gen_ack_i;
  assign {rcstage_bits,rcstage_rc,rcstage_fips} = sfifo_rcstage_rdata;


  assign ctr_drbg_gen_sfifo_grcstage_err_o =
         {(sfifo_rcstage_push && !sfifo_rcstage_not_full),
          (sfifo_rcstage_pop && !sfifo_rcstage_not_empty),
          (!sfifo_rcstage_not_full && !sfifo_rcstage_not_empty)};

  assign gen_upd_rdy_o = sfifo_rcstage_not_empty && sfifo_genbits_not_full;


  //--------------------------------------------
  // final cmd block processing
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(GenbitsFifoWidth),
    .Pass(0),
    .Depth(GenbitsFifoDepth)
  ) u_prim_fifo_sync_genbits (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_gen_enable_i),
    .wvalid_i       (sfifo_genbits_push),
    .wready_o       (sfifo_genbits_not_full),
    .wdata_i        (sfifo_genbits_wdata),
    .rvalid_o       (sfifo_genbits_not_empty),
    .rready_i       (sfifo_genbits_pop),
    .rdata_o        (sfifo_genbits_rdata),
    .depth_o        ()
  );

  assign sfifo_genbits_push = sfifo_rcstage_pop;

  assign rcstage_rc_plus1 = (rcstage_rc+1);

  assign sfifo_genbits_wdata =
         {rcstage_fips,rcstage_bits,upd_gen_key_i,upd_gen_v_i,
          rcstage_rc_plus1,upd_gen_inst_id_i,upd_gen_ccmd_i};

  assign sfifo_genbits_pop = ctr_drbg_gen_rdy_i && sfifo_genbits_not_empty;
  assign {ctr_drbg_gen_fips_o,ctr_drbg_gen_bits_o,
          ctr_drbg_gen_key_o,ctr_drbg_gen_v_o,ctr_drbg_gen_rc_o,
          ctr_drbg_gen_inst_id_o,ctr_drbg_gen_ccmd_o} = sfifo_genbits_rdata;

  assign ctr_drbg_gen_sfifo_ggenbits_err_o =
         {(sfifo_genbits_push && !sfifo_genbits_not_full),
         (sfifo_genbits_pop && !sfifo_genbits_not_empty),
         (!sfifo_genbits_not_full && !sfifo_genbits_not_empty)};

  // block ack
  assign ctr_drbg_gen_ack_o = sfifo_genbits_pop;

  assign ctr_drbg_gen_sts_o = sfifo_genbits_pop && (
         (ctr_drbg_gen_ccmd_o == INV) ||
         (ctr_drbg_gen_ccmd_o == INS) ||
         (ctr_drbg_gen_ccmd_o == RES) ||
         (ctr_drbg_gen_ccmd_o == UPD) ||
         (ctr_drbg_gen_ccmd_o == UNI));


endmodule
