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
  parameter int NApps = 4,
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
  input logic                ctr_drbg_gen_glast_i,   // gen cmd last beat
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

   // es_req/ack
  input logic                ctr_drbg_gen_es_req_i,
  output logic               ctr_drbg_gen_es_ack_o,

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
  output logic               ctr_drbg_gen_v_ctr_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_gbencack_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_grcstage_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_ggenreq_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_gadstage_err_o,
  output logic [2:0]         ctr_drbg_gen_sfifo_ggenbits_err_o,
  output logic               ctr_drbg_gen_sm_err_o
);

  localparam int GenreqFifoDepth = 1;
  localparam int GenreqFifoWidth = KeyLen+BlkLen+CtrLen+1+SeedLen+1+StateId+Cmd;
  localparam int BlkEncAckFifoDepth = 1;
  localparam int BlkEncAckFifoWidth = BlkLen+StateId+Cmd;
  localparam int AdstageFifoDepth = 1;
  localparam int AdstageFifoWidth = KeyLen+BlkLen+CtrLen+1+1;
  localparam int RCStageFifoDepth = 1;
  localparam int RCStageFifoWidth = KeyLen+BlkLen+BlkLen+CtrLen+1+1+StateId+Cmd;
  localparam int GenbitsFifoDepth = 1;
  localparam int GenbitsFifoWidth = 1+BlkLen+KeyLen+BlkLen+CtrLen+StateId+Cmd;

  // signals
  logic [Cmd-1:0]     genreq_ccmd;
  logic [StateId-1:0] genreq_id;
  logic               genreq_glast;
  logic [SeedLen-1:0] genreq_adata;
  logic               genreq_fips;
  logic [KeyLen-1:0]  genreq_key;
  logic [BlkLen-1:0]  genreq_v;
  logic [CtrLen-1:0]  genreq_rc;

  logic [KeyLen-1:0]  adstage_key;
  logic [BlkLen-1:0]  adstage_v;
  logic [CtrLen-1:0]  adstage_rc;
  logic               adstage_fips;
  logic               adstage_glast;
  logic [SeedLen-1:0] adstage_adata;

  logic [KeyLen-1:0]  rcstage_key;
  logic [BlkLen-1:0]  rcstage_v;
  logic [BlkLen-1:0]  rcstage_bits;
  logic [CtrLen-1:0]  rcstage_rc;
  logic               rcstage_glast;
  logic               rcstage_fips;
  logic [CtrLen-1:0]  rcstage_rc_plus1;
  logic [Cmd-1:0]     rcstage_ccmd;
  logic [StateId-1:0] rcstage_inst_id;

  logic [Cmd-1:0]     genreq_ccmd_modified;
  logic [Cmd-1:0]     bencack_ccmd_modified;

  // cmdreq fifo
  // logic [$clog2(CmdreqFifoDepth):0] sfifo_cmdreq_depth;
  logic [GenreqFifoWidth-1:0] sfifo_genreq_rdata;
  logic                       sfifo_genreq_push;
  logic [GenreqFifoWidth-1:0] sfifo_genreq_wdata;
  logic                       sfifo_genreq_pop;
  logic                       sfifo_genreq_full;
  logic                       sfifo_genreq_not_empty;

  // adstage fifo
  logic [AdstageFifoWidth-1:0] sfifo_adstage_rdata;
  logic                        sfifo_adstage_push;
  logic [AdstageFifoWidth-1:0] sfifo_adstage_wdata;
  logic                        sfifo_adstage_pop;
  logic                        sfifo_adstage_full;
  logic                        sfifo_adstage_not_empty;
  // blk_encrypt_ack fifo
  logic [BlkEncAckFifoWidth-1:0] sfifo_bencack_rdata;
  logic                       sfifo_bencack_push;
  logic [BlkEncAckFifoWidth-1:0] sfifo_bencack_wdata;
  logic                       sfifo_bencack_pop;
  logic                       sfifo_bencack_full;
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
  logic                        sfifo_rcstage_full;
  logic                        sfifo_rcstage_not_empty;

  // genbits fifo
  logic [GenbitsFifoWidth-1:0] sfifo_genbits_rdata;
  logic                        sfifo_genbits_push;
  logic [GenbitsFifoWidth-1:0] sfifo_genbits_wdata;
  logic                        sfifo_genbits_pop;
  logic                        sfifo_genbits_full;
  logic                        sfifo_genbits_not_empty;

  logic [CtrLen-1:0]           v_inc;
  logic [BlkLen-1:0]           v_first;
  logic [BlkLen-1:0]           v_sized;
  logic                        v_ctr_load;
  logic                        v_ctr_inc;
  logic                        interate_ctr_done;
  logic                        interate_ctr_inc;
  logic [NApps-1:0]            capt_adata;
  logic [SeedLen-1:0]          update_adata[NApps];
  logic [CtrLen-1:0]           v_ctr;

  // flops
  logic [1:0]                  interate_ctr_q, interate_ctr_d;
  logic [SeedLen-1:0]          update_adata_q[NApps], update_adata_d[NApps];
  logic [NApps-1:0]            update_adata_vld_q, update_adata_vld_d;

// Encoding generated with:
// $ ./util/design/sparse-fsm-encode.py -d 3 -m 4 -n 5 \
//      -s 2651202796 --language=sv
//
// Hamming distance histogram:
//
//  0: --
//  1: --
//  2: --
//  3: |||||||||||||||||||| (66.67%)
//  4: |||||||||| (33.33%)
//  5: --
//
// Minimum Hamming distance: 3
// Maximum Hamming distance: 4
// Minimum Hamming weight: 2
// Maximum Hamming weight: 3
//

  localparam int StateWidth = 5;
  typedef enum logic [StateWidth-1:0] {
    ReqIdle  = 5'b01101,
    ReqSend  = 5'b00011,
    ESHalt   = 5'b11000,
    ReqError = 5'b10110
} state_e;

  state_e state_d, state_q;

  // SEC_CM: UPDATE.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, ReqIdle)

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      interate_ctr_q     <= '0;
      update_adata_q     <= '{default:0};
      update_adata_vld_q <= '{default:0};
    end else begin
      interate_ctr_q     <= interate_ctr_d;
      update_adata_q     <= update_adata_d;
      update_adata_vld_q <= update_adata_vld_d;
    end



  //--------------------------------------------
  // input request fifo for staging gen request
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(GenreqFifoWidth),
    .Pass(0),
    .Depth(GenreqFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_genreq (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_gen_enable_i),
    .wvalid_i       (sfifo_genreq_push),
    .wready_o       (),
    .wdata_i        (sfifo_genreq_wdata),
    .rvalid_o       (sfifo_genreq_not_empty),
    .rready_i       (sfifo_genreq_pop),
    .rdata_o        (sfifo_genreq_rdata),
    .full_o         (sfifo_genreq_full),
    .depth_o        (),
    .err_o          ()
  );

  assign genreq_ccmd_modified = (ctr_drbg_gen_ccmd_i == GEN) ? GENB : INV;

  assign sfifo_genreq_wdata = {ctr_drbg_gen_key_i,ctr_drbg_gen_v_i,ctr_drbg_gen_rc_i,
                               ctr_drbg_gen_fips_i,ctr_drbg_gen_adata_i,ctr_drbg_gen_glast_i,
                               ctr_drbg_gen_inst_id_i,genreq_ccmd_modified};

  assign sfifo_genreq_push = ctr_drbg_gen_enable_i && ctr_drbg_gen_req_i;

  assign {genreq_key,genreq_v,genreq_rc,
          genreq_fips,genreq_adata,genreq_glast,
          genreq_id,genreq_ccmd} = sfifo_genreq_rdata;

  assign ctr_drbg_gen_rdy_o = !sfifo_genreq_full;

  assign ctr_drbg_gen_sfifo_ggenreq_err_o =
         {(sfifo_genreq_push && sfifo_genreq_full),
          (sfifo_genreq_pop && !sfifo_genreq_not_empty),
          (sfifo_genreq_full && !sfifo_genreq_not_empty)};



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

  // SEC_CM: DRBG_GEN.CTR.REDUN
  prim_count #(
    .Width(CtrLen)
  ) u_prim_count_ctr_drbg (
    .clk_i,
    .rst_ni,
    .clr_i(!ctr_drbg_gen_enable_i),
    .set_i(v_ctr_load),
    .set_cnt_i(v_first[CtrLen-1:0]),
    .incr_en_i(v_ctr_inc), // count up
    .decr_en_i(1'b0),
    .step_i(CtrLen'(1)),
    .cnt_o(v_ctr),
    .cnt_next_o(),
    .err_o(ctr_drbg_gen_v_ctr_err_o)
  );

  assign v_sized = {v_first[BlkLen-1:CtrLen],v_ctr};

  // interation counter
  assign interate_ctr_d =
         (!ctr_drbg_gen_enable_i) ? '0 :
         interate_ctr_done ? '0 :
         interate_ctr_inc ? (interate_ctr_q + 1) :
         interate_ctr_q;

  // Supporting only 128b requests
  assign interate_ctr_done = (interate_ctr_q >= 2'(BlkLen/BlkLen));

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
    ctr_drbg_gen_sm_err_o = 1'b0;
    ctr_drbg_gen_es_ack_o = 1'b0;
    unique case (state_q)
      // ReqIdle: increment v this cycle, push in next
      ReqIdle: begin
        // Prioritize halt requests from entropy_src over disable, as CSRNG would otherwise starve
        // those requests while it is idle.
        if (ctr_drbg_gen_es_req_i) begin
          state_d = ESHalt;
        end else if (!ctr_drbg_gen_enable_i) begin
          state_d = ReqIdle;
        end else if (sfifo_genreq_not_empty && !sfifo_adstage_full) begin
          v_ctr_load = 1'b1;
          state_d = ReqSend;
        end
      end
      ReqSend: begin
        if (!ctr_drbg_gen_enable_i) begin
          state_d = ReqIdle;
        end else if (!interate_ctr_done) begin
          block_encrypt_req_o = 1'b1;
          sfifo_adstage_push = 1'b1;
          if (block_encrypt_rdy_i) begin
            v_ctr_inc  = 1'b1;
            interate_ctr_inc  = 1'b1;
          end
        end else begin
          sfifo_genreq_pop = 1'b1;
          state_d = ReqIdle;
        end
      end
      ESHalt: begin
        ctr_drbg_gen_es_ack_o = 1'b1;
        if (!ctr_drbg_gen_es_req_i) begin
          state_d = ReqIdle;
        end
      end
      ReqError: begin
        ctr_drbg_gen_sm_err_o = 1'b1;
      end
      default: begin
        state_d = ReqError;
        ctr_drbg_gen_sm_err_o = 1'b1;
      end
    endcase
  end


  //--------------------------------------------
  // fifo to stage key, v, rc, and adata, waiting for update block to ack
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(AdstageFifoWidth),
    .Pass(0),
    .Depth(AdstageFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_adstage (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_gen_enable_i),
    .wvalid_i       (sfifo_adstage_push),
    .wready_o       (),
    .wdata_i        (sfifo_adstage_wdata),
    .rvalid_o       (sfifo_adstage_not_empty),
    .rready_i       (sfifo_adstage_pop),
    .rdata_o        (sfifo_adstage_rdata),
    .full_o         (sfifo_adstage_full),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_adstage_wdata = {genreq_key,v_sized,genreq_rc,genreq_fips,genreq_glast};
  assign sfifo_adstage_pop = sfifo_adstage_not_empty && sfifo_bencack_pop;
  assign {adstage_key,adstage_v,adstage_rc,adstage_fips,adstage_glast} = sfifo_adstage_rdata;

  assign ctr_drbg_gen_sfifo_gadstage_err_o =
         {(sfifo_adstage_push && sfifo_adstage_full),
          (sfifo_adstage_pop && !sfifo_adstage_not_empty),
          (sfifo_adstage_full && !sfifo_adstage_not_empty)};


  // array to hold each channel's adata
  for (genvar i = 0; i < NApps; i = i+1) begin : gen_adata
    assign capt_adata[i] = (sfifo_adstage_push && (genreq_id == i));

    assign update_adata_vld_d[i] = ~ctr_drbg_gen_enable_i ? 1'b0 :
           capt_adata[i] && !update_adata_vld_q[i] ? 1'b1 :
           (gen_upd_req_o && upd_gen_rdy_i && (sfifo_bencack_inst_id == i)) ? 1'b0 :
           update_adata_vld_q[i];

    assign update_adata_d[i] = ~ctr_drbg_gen_enable_i ? '0 :
                               (capt_adata[i] && !update_adata_vld_q[i]) ? genreq_adata :
                               update_adata_q[i];
    assign update_adata[i] = update_adata_q[i] & {SeedLen{update_adata_vld_q[i] &&
                                                          (genreq_id == i)}};
  end

  always_comb begin
    adstage_adata = '0;
    for (int i = 0; i < NApps; i = i+1) begin
      // since only one bus is active at a time based on the instant id,
      // an "or" of all the buses can be done below
      adstage_adata |= update_adata[i];
    end
  end


  //--------------------------------------------
  // block_encrypt response fifo from block encrypt
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(BlkEncAckFifoWidth),
    .Pass(0),
    .Depth(BlkEncAckFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_bencack (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .clr_i    (!ctr_drbg_gen_enable_i),
    .wvalid_i (sfifo_bencack_push),
    .wready_o (),
    .wdata_i  (sfifo_bencack_wdata),
    .rvalid_o (sfifo_bencack_not_empty),
    .rready_i (sfifo_bencack_pop),
    .rdata_o  (sfifo_bencack_rdata),
    .full_o   (sfifo_bencack_full),
    .depth_o  (),
    .err_o    ()
  );

  assign bencack_ccmd_modified = (block_encrypt_ccmd_i == GENB) ? GENU : INV;

  assign sfifo_bencack_push = !sfifo_bencack_full && block_encrypt_ack_i;
  assign sfifo_bencack_wdata = {block_encrypt_v_i,block_encrypt_inst_id_i,bencack_ccmd_modified};
  assign block_encrypt_rdy_o = !sfifo_bencack_full;

  assign sfifo_bencack_pop = !sfifo_rcstage_full && sfifo_bencack_not_empty &&
                             (upd_gen_rdy_i || !adstage_glast);

  assign {sfifo_bencack_bits,sfifo_bencack_inst_id,sfifo_bencack_ccmd} = sfifo_bencack_rdata;

  assign ctr_drbg_gen_sfifo_gbencack_err_o =
         {(sfifo_bencack_push && sfifo_bencack_full),
          (sfifo_bencack_pop && !sfifo_bencack_not_empty),
          (sfifo_bencack_full && !sfifo_bencack_not_empty)};


  //--------------------------------------------
  // prepare values for update step
  //--------------------------------------------

  // send to the update block
  assign gen_upd_req_o = sfifo_bencack_not_empty && adstage_glast;
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
    .Depth(RCStageFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_rcstage (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_gen_enable_i),
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

  assign sfifo_rcstage_push = sfifo_adstage_pop;
  assign sfifo_rcstage_wdata = {adstage_key,adstage_v,sfifo_bencack_bits,
                                adstage_rc,adstage_fips,adstage_glast,
                                sfifo_bencack_inst_id,sfifo_bencack_ccmd};

  assign sfifo_rcstage_pop = sfifo_rcstage_not_empty && (upd_gen_ack_i || !rcstage_glast);

  assign {rcstage_key,rcstage_v,rcstage_bits,rcstage_rc,rcstage_fips,rcstage_glast,
          rcstage_inst_id,rcstage_ccmd} = sfifo_rcstage_rdata;


  assign ctr_drbg_gen_sfifo_grcstage_err_o =
         {(sfifo_rcstage_push && sfifo_rcstage_full),
          (sfifo_rcstage_pop && !sfifo_rcstage_not_empty),
          (sfifo_rcstage_full && !sfifo_rcstage_not_empty)};

  assign gen_upd_rdy_o = sfifo_rcstage_not_empty && !sfifo_genbits_full;


  //--------------------------------------------
  // final cmd block processing
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(GenbitsFifoWidth),
    .Pass(0),
    .Depth(GenbitsFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_genbits (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .clr_i          (!ctr_drbg_gen_enable_i),
    .wvalid_i       (sfifo_genbits_push),
    .wready_o       (),
    .wdata_i        (sfifo_genbits_wdata),
    .rvalid_o       (sfifo_genbits_not_empty),
    .rready_i       (sfifo_genbits_pop),
    .rdata_o        (sfifo_genbits_rdata),
    .full_o         (sfifo_genbits_full),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_genbits_push = sfifo_rcstage_pop;

  assign rcstage_rc_plus1 = (rcstage_rc+1);

  assign sfifo_genbits_wdata = rcstage_glast ?
                               {rcstage_fips,rcstage_bits,upd_gen_key_i,upd_gen_v_i,
                                rcstage_rc_plus1,upd_gen_inst_id_i,upd_gen_ccmd_i} :
                               {rcstage_fips,rcstage_bits,rcstage_key,rcstage_v,
                                rcstage_rc,rcstage_inst_id,rcstage_ccmd};

  assign sfifo_genbits_pop = ctr_drbg_gen_rdy_i && sfifo_genbits_not_empty;
  assign {ctr_drbg_gen_fips_o,ctr_drbg_gen_bits_o,
          ctr_drbg_gen_key_o,ctr_drbg_gen_v_o,ctr_drbg_gen_rc_o,
          ctr_drbg_gen_inst_id_o,ctr_drbg_gen_ccmd_o} = sfifo_genbits_rdata;

  assign ctr_drbg_gen_sfifo_ggenbits_err_o =
         {(sfifo_genbits_push && sfifo_genbits_full),
         (sfifo_genbits_pop && !sfifo_genbits_not_empty),
         (sfifo_genbits_full && !sfifo_genbits_not_empty)};

  // block ack
  assign ctr_drbg_gen_ack_o = sfifo_genbits_pop;

  assign ctr_drbg_gen_sts_o = sfifo_genbits_pop && (
         (ctr_drbg_gen_ccmd_o == INV) ||
         (ctr_drbg_gen_ccmd_o == INS) ||
         (ctr_drbg_gen_ccmd_o == RES) ||
         (ctr_drbg_gen_ccmd_o == UPD) ||
         (ctr_drbg_gen_ccmd_o == UNI));

  // Make sure that the state machine has a stable error state. This means that after the error
  // state is entered it will not exit it unless a reset signal is received.
  `ASSERT(CsrngDrbgGenErrorStStable_A, state_q == ReqError |=> $stable(state_q))
  // If in error state, the error output must be high.
  `ASSERT(CsrngDrbgGenErrorOutput_A,
          !(state_q inside {ReqIdle, ReqSend, ESHalt}) |-> ctr_drbg_gen_sm_err_o)
endmodule
