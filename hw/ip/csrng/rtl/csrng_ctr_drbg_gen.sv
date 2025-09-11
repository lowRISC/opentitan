// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng ctr_drbg generate module
//
// This module will process the second half of the generate function.
// It takes in the key, v, and reseed counter values processed by the
// ctr_drbg cmd module.

`include "prim_assert.sv"

module csrng_ctr_drbg_gen import csrng_pkg::*; (
  input  logic clk_i,
  input  logic rst_ni,

  // Global enable
  input  logic enable_i,

  // Command interface
  // Request in from ctr_drbg_cmd
  input  logic                   cmd_req_vld_i,
  output logic                   cmd_req_rdy_o,
  input  csrng_core_data_t       cmd_req_data_i,
  input  logic                   cmd_req_glast_i,

  // Response out to state_db
  output logic                   ctr_drbg_gen_ack_o, // final ack when update process is completed
  input  logic                   ctr_drbg_gen_rdy_i, // ready to process the ack above
  output csrng_cmd_sts_e         ctr_drbg_gen_sts_o, // final ack status
  output logic [CmdWidth-1:0]    ctr_drbg_gen_ccmd_o,
  output logic [InstIdWidth-1:0] ctr_drbg_gen_inst_id_o,
  output logic [KeyLen-1:0]      ctr_drbg_gen_key_o,
  output logic [BlkLen-1:0]      ctr_drbg_gen_v_o,
  output logic [CtrLen-1:0]      ctr_drbg_gen_rc_o,
  output logic [BlkLen-1:0]      ctr_drbg_gen_bits_o,
  output logic                   ctr_drbg_gen_fips_o,

  // Halt request from entropy source
  input  logic                   es_halt_req_i,
  output logic                   es_halt_ack_o,

  // Update request interface
  output logic                   gen_upd_req_vld_o,
  input  logic                   gen_upd_req_rdy_i,
  output csrng_upd_data_t        gen_upd_req_data_o,

  // Update response interface
  input  logic                   gen_upd_rsp_vld_i,
  output logic                   gen_upd_rsp_rdy_o,
  input  csrng_upd_data_t        gen_upd_rsp_data_i,

  // Block encrypt interface
  output logic                   block_encrypt_req_vld_o,
  input  logic                   block_encrypt_req_rdy_i,
  output csrng_benc_data_t       block_encrypt_req_data_o,

  input  logic                   block_encrypt_ack_i,
  output logic                   block_encrypt_rdy_o,
  input  logic [CmdWidth-1:0]    block_encrypt_ccmd_i,
  input  logic [InstIdWidth-1:0] block_encrypt_inst_id_i,
  input  logic [BlkLen-1:0]      block_encrypt_v_i,

  // error status signals
  output logic                   ctr_err_o,
  output logic                   sm_err_o,
  output logic [2:0]             fifo_gbencack_err_o,
  output logic [2:0]             fifo_grcstage_err_o,
  output logic [2:0]             fifo_ggenreq_err_o,
  output logic [2:0]             fifo_gadstage_err_o,
  output logic [2:0]             fifo_ggenbits_err_o
);

  import csrng_reg_pkg::NumApps;

  localparam int GenreqFifoWidth = CoreDataWidth + 1;
  localparam int BlkEncAckFifoDepth = 1;
  localparam int BlkEncAckFifoWidth = BlkLen+InstIdWidth+CmdWidth;
  localparam int AdstageFifoDepth = 1;
  localparam int AdstageFifoWidth = KeyLen+BlkLen+CtrLen+1+1;
  localparam int RCStageFifoDepth = 1;
  localparam int RCStageFifoWidth = KeyLen+BlkLen+BlkLen+CtrLen+1+1+InstIdWidth+CmdWidth;
  localparam int GenbitsFifoDepth = 1;
  localparam int GenbitsFifoWidth = 1+BlkLen+KeyLen+BlkLen+CtrLen+InstIdWidth+CmdWidth;

  // signals
  logic             genreq_glast;
  csrng_core_data_t genreq_data;

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
  logic [CmdWidth-1:0]rcstage_ccmd;
  logic [InstIdWidth-1:0] rcstage_inst_id;

  logic [CmdWidth-1:0]bencack_ccmd_modified;

  // cmdreq fifo
  logic [GenreqFifoWidth-1:0] sfifo_genreq_rdata;
  logic                       sfifo_genreq_wvld;
  logic                       sfifo_genreq_wrdy;
  logic [GenreqFifoWidth-1:0] sfifo_genreq_wdata;
  logic                       sfifo_genreq_rrdy;
  logic                       sfifo_genreq_rvld;

  // adstage fifo
  logic [AdstageFifoWidth-1:0] sfifo_adstage_rdata;
  logic                        sfifo_adstage_wvld;
  logic                        sfifo_adstage_wrdy;
  logic [AdstageFifoWidth-1:0] sfifo_adstage_wdata;
  logic                        sfifo_adstage_rrdy;
  logic                        sfifo_adstage_rvld;
  // blk_encrypt_ack fifo
  logic [BlkEncAckFifoWidth-1:0] sfifo_bencack_rdata;
  logic                       sfifo_bencack_wvld;
  logic                       sfifo_bencack_wrdy;
  logic [BlkEncAckFifoWidth-1:0] sfifo_bencack_wdata;
  logic                       sfifo_bencack_rrdy;
  logic                       sfifo_bencack_rvld;
  // breakout
  logic [CmdWidth-1:0]        sfifo_bencack_ccmd;
  logic [InstIdWidth-1:0]     sfifo_bencack_inst_id;
  logic [BlkLen-1:0]          sfifo_bencack_bits;

  // rcstage fifo
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_rdata;
  logic                        sfifo_rcstage_wvld;
  logic                        sfifo_rcstage_wrdy;
  logic [RCStageFifoWidth-1:0] sfifo_rcstage_wdata;
  logic                        sfifo_rcstage_rrdy;
  logic                        sfifo_rcstage_rvld;

  // genbits fifo
  logic [GenbitsFifoWidth-1:0] sfifo_genbits_rdata;
  logic                        sfifo_genbits_wvld;
  logic                        sfifo_genbits_wrdy;
  logic [GenbitsFifoWidth-1:0] sfifo_genbits_wdata;
  logic                        sfifo_genbits_rrdy;
  logic                        sfifo_genbits_rvld;

  logic [BlkLen-1:0]           v_load;
  logic [BlkLen-1:0]           v_ctr_sized;
  logic                        v_ctr_load;
  logic                        v_ctr_inc;
  logic [NumApps-1:0]          capt_adata;
  logic [SeedLen-1:0]          update_adata[NumApps];
  logic [CtrLen-1:0]           v_ctr;

  // status error signals
  logic                        ctr_drbg_gen_sts_err;

  // flops
  logic [SeedLen-1:0]          update_adata_q[NumApps], update_adata_d[NumApps];
  logic [NumApps-1:0]          update_adata_vld_q, update_adata_vld_d;

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

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      update_adata_q     <= '{default:0};
      update_adata_vld_q <= '{default:0};
    end else begin
      update_adata_q     <= update_adata_d;
      update_adata_vld_q <= update_adata_vld_d;
    end
  end

  //--------------------------------------------
  // input request fifo for staging gen request
  //--------------------------------------------

  csrng_core_data_t cmd_req_data_fifo;

  prim_fifo_sync #(
    .Width            (GenreqFifoWidth),
    .Pass             (0),
    .Depth            (1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_genreq (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_genreq_wvld),
    .wready_o(sfifo_genreq_wrdy),
    .wdata_i (sfifo_genreq_wdata),
    .rvalid_o(sfifo_genreq_rvld),
    .rready_i(sfifo_genreq_rrdy),
    .rdata_o (sfifo_genreq_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  // Change the command code to an internal one for proper routing in csrng_core
  always_comb begin
    cmd_req_data_fifo = cmd_req_data_i;
    cmd_req_data_fifo.cmd = (cmd_req_data_i.cmd == GEN) ? GENB : INV;
  end

  assign sfifo_genreq_wdata = {cmd_req_glast_i,
                               cmd_req_data_fifo};

  assign sfifo_genreq_wvld = enable_i && cmd_req_vld_i;
  assign cmd_req_rdy_o = sfifo_genreq_wrdy;

  assign {genreq_glast,
          genreq_data} = sfifo_genreq_rdata;

  assign fifo_ggenreq_err_o =
         {( sfifo_genreq_wvld && !sfifo_genreq_wrdy),
          ( sfifo_genreq_rrdy && !sfifo_genreq_rvld),
          (!sfifo_genreq_wrdy && !sfifo_genreq_rvld)};


  //--------------------------------------------
  // prepare value for block_encrypt step
  //--------------------------------------------

  // TODO(#28153) check if the (additional) increment here is really necessary and whether it
  // violates the redundant counter encoding listed as a SEC_CM below.
  if (CtrLen < BlkLen) begin : g_ctr_load_lsb
    logic [CtrLen-1:0] v_inc;
    assign v_inc  = genreq_data.v[CtrLen-1:0] + 1;
    assign v_load = {genreq_data.v[BlkLen-1:CtrLen], v_inc};
  end else begin : g_ctr_load_full
    assign v_load = genreq_data.v + 1;
  end

  // SEC_CM: DRBG_GEN.CTR.REDUN
  prim_count #(
    .Width(CtrLen)
  ) u_prim_count_ctr_drbg (
    .clk_i,
    .rst_ni,

    .clr_i    (!enable_i),
    .set_i    (v_ctr_load),
    .set_cnt_i(v_load[CtrLen-1:0]),

    .incr_en_i(v_ctr_inc),
    .decr_en_i(1'b0),
    .step_i   (CtrLen'(1)),
    .commit_i (1'b1),

    .cnt_o             (v_ctr),
    .cnt_after_commit_o(),
    .err_o             (ctr_err_o)
  );

  // Combine the MSBs of the initial v from the state db with the current counter value as LSBs
  if (CtrLen < BlkLen) begin : g_ctr_sized_lsb
    assign v_ctr_sized = {v_load[BlkLen-1:CtrLen], v_ctr};
  end else begin : g_ctr_sized_full
    // Need to distinguish this case as the slice select into v_load above would otherwise yield an
    // incorrect range ([BlkLen-1:BlkLen])
    assign v_ctr_sized = v_ctr;
  end

  //--------------------------------------------
  // state machine to send values to block_encrypt
  //--------------------------------------------

  // Send genreq data with the altered v
  assign block_encrypt_req_data_o = '{
    inst_id: genreq_data.inst_id,
    cmd:     genreq_data.cmd,
    key:     genreq_data.key,
    v:       v_ctr_sized
  };

  always_comb begin
    state_d = state_q;
    v_ctr_load = 1'b0;
    v_ctr_inc  = 1'b0;
    sfifo_adstage_wvld = 1'b0;
    block_encrypt_req_vld_o = 1'b0;
    sfifo_genreq_rrdy = 1'b0;
    sm_err_o = 1'b0;
    es_halt_ack_o = 1'b0;
    unique case (state_q)
      // ReqIdle: increment v this cycle, push in next
      ReqIdle: begin
        // Prioritize halt requests from entropy_src over disable, as CSRNG would otherwise starve
        // those requests while it is idle.
        if (es_halt_req_i) begin
          state_d = ESHalt;
        end else if (!enable_i) begin
          state_d = ReqIdle;
        end else if (sfifo_genreq_rvld && sfifo_adstage_wrdy) begin
          v_ctr_load = 1'b1;
          state_d = ReqSend;
        end
      end
      ReqSend: begin
        if (!enable_i) begin
          state_d = ReqIdle;
        end else begin
          block_encrypt_req_vld_o = 1'b1;
          if (block_encrypt_req_rdy_i) begin
            // Write to adstage and empty the genreq FIFO
            sfifo_adstage_wvld = 1'b1;
            sfifo_genreq_rrdy  = 1'b1;
            // Increment v & back to idle
            v_ctr_inc = 1'b1;
            state_d   = ReqIdle;
          end
        end
      end
      ESHalt: begin
        es_halt_ack_o = 1'b1;
        if (!es_halt_req_i) begin
          state_d = ReqIdle;
        end
      end
      ReqError: begin
        sm_err_o = 1'b1;
      end
      default: begin
        state_d = ReqError;
        sm_err_o = 1'b1;
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
    .clr_i          (!enable_i),
    .wvalid_i       (sfifo_adstage_wvld),
    .wready_o       (sfifo_adstage_wrdy),
    .wdata_i        (sfifo_adstage_wdata),
    .rvalid_o       (sfifo_adstage_rvld),
    .rready_i       (sfifo_adstage_rrdy),
    .rdata_o        (sfifo_adstage_rdata),
    .full_o         (),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_adstage_wdata = {genreq_data.key,v_ctr_sized,genreq_data.rs_ctr,genreq_data.fips,genreq_glast};
  assign sfifo_adstage_rrdy = sfifo_adstage_rvld && sfifo_bencack_rrdy;
  assign {adstage_key,adstage_v,adstage_rc,adstage_fips,adstage_glast} = sfifo_adstage_rdata;

  assign fifo_gadstage_err_o =
         {( sfifo_adstage_wvld && !sfifo_adstage_wrdy),
          ( sfifo_adstage_rrdy && !sfifo_adstage_rvld),
          (!sfifo_adstage_wrdy && !sfifo_adstage_rvld)};


  // array to hold each channel's adata
  for (genvar i = 0; i < NumApps; i = i+1) begin : gen_adata
    assign capt_adata[i] = (sfifo_adstage_wvld && (genreq_data.inst_id == i));

    assign update_adata_vld_d[i] = ~enable_i ? 1'b0 :
           capt_adata[i] && !update_adata_vld_q[i] ? 1'b1 :
           (gen_upd_req_vld_o && gen_upd_req_rdy_i && (sfifo_bencack_inst_id == i)) ? 1'b0 :
           update_adata_vld_q[i];

    assign update_adata_d[i] = ~enable_i ? '0 :
                               (capt_adata[i] && !update_adata_vld_q[i]) ? genreq_data.pdata :
                               update_adata_q[i];
    assign update_adata[i] = update_adata_q[i] & {SeedLen{update_adata_vld_q[i] &&
                                                          (genreq_data.inst_id == i)}};
  end

  always_comb begin
    adstage_adata = '0;
    for (int i = 0; i < NumApps; i = i+1) begin
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
    .clr_i    (!enable_i),
    .wvalid_i (sfifo_bencack_wvld),
    .wready_o (sfifo_bencack_wrdy),
    .wdata_i  (sfifo_bencack_wdata),
    .rvalid_o (sfifo_bencack_rvld),
    .rready_i (sfifo_bencack_rrdy),
    .rdata_o  (sfifo_bencack_rdata),
    .full_o   (),
    .depth_o  (),
    .err_o    ()
  );

  assign bencack_ccmd_modified = (block_encrypt_ccmd_i == GENB) ? GENU : INV;

  assign sfifo_bencack_wvld = sfifo_bencack_wrdy && block_encrypt_ack_i;
  assign sfifo_bencack_wdata = {block_encrypt_v_i,block_encrypt_inst_id_i,bencack_ccmd_modified};
  assign block_encrypt_rdy_o = sfifo_bencack_wrdy;

  assign sfifo_bencack_rrdy = sfifo_rcstage_wrdy && sfifo_bencack_rvld &&
                             (gen_upd_req_rdy_i || !adstage_glast);

  assign {sfifo_bencack_bits,sfifo_bencack_inst_id,sfifo_bencack_ccmd} = sfifo_bencack_rdata;

  assign fifo_gbencack_err_o =
         {( sfifo_bencack_wvld && !sfifo_bencack_wrdy),
          ( sfifo_bencack_rrdy && !sfifo_bencack_rvld),
          (!sfifo_bencack_wrdy && !sfifo_bencack_rvld)};


  //--------------------------------------------
  // prepare values for update step
  //--------------------------------------------

  // send to the update block
  assign gen_upd_req_vld_o = sfifo_bencack_rvld && adstage_glast;
  assign gen_upd_req_data_o = '{
    inst_id: sfifo_bencack_inst_id,
    cmd:     sfifo_bencack_ccmd,
    key:     adstage_key,
    v:       adstage_v,
    pdata:   adstage_adata
  };



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
    .clr_i          (!enable_i),
    .wvalid_i       (sfifo_rcstage_wvld),
    .wready_o       (sfifo_rcstage_wrdy),
    .wdata_i        (sfifo_rcstage_wdata),
    .rvalid_o       (sfifo_rcstage_rvld),
    .rready_i       (sfifo_rcstage_rrdy),
    .rdata_o        (sfifo_rcstage_rdata),
    .full_o         (),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_rcstage_wvld = sfifo_adstage_rrdy;
  assign sfifo_rcstage_wdata = {adstage_key,adstage_v,sfifo_bencack_bits,
                                adstage_rc,adstage_fips,adstage_glast,
                                sfifo_bencack_inst_id,sfifo_bencack_ccmd};

  assign sfifo_rcstage_rrdy = sfifo_rcstage_rvld && (gen_upd_rsp_vld_i || !rcstage_glast);

  assign {rcstage_key,rcstage_v,rcstage_bits,rcstage_rc,rcstage_fips,rcstage_glast,
          rcstage_inst_id,rcstage_ccmd} = sfifo_rcstage_rdata;


  assign fifo_grcstage_err_o =
         {( sfifo_rcstage_wvld && !sfifo_rcstage_wrdy),
          ( sfifo_rcstage_rrdy && !sfifo_rcstage_rvld),
          (!sfifo_rcstage_wrdy && !sfifo_rcstage_rvld)};

  assign gen_upd_rsp_rdy_o = sfifo_rcstage_rvld && sfifo_genbits_wrdy;


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
    .clr_i          (!enable_i),
    .wvalid_i       (sfifo_genbits_wvld),
    .wready_o       (sfifo_genbits_wrdy),
    .wdata_i        (sfifo_genbits_wdata),
    .rvalid_o       (sfifo_genbits_rvld),
    .rready_i       (sfifo_genbits_rrdy),
    .rdata_o        (sfifo_genbits_rdata),
    .full_o         (),
    .depth_o        (),
    .err_o          ()
  );

  assign sfifo_genbits_wvld = sfifo_rcstage_rrdy;

  assign rcstage_rc_plus1 = (rcstage_rc+1);

  assign sfifo_genbits_wdata = rcstage_glast ?
                               {rcstage_fips,
                                rcstage_bits,
                                gen_upd_rsp_data_i.key,
                                gen_upd_rsp_data_i.v,
                                rcstage_rc_plus1,
                                gen_upd_rsp_data_i.inst_id,
                                gen_upd_rsp_data_i.cmd} :
                               {rcstage_fips,rcstage_bits,rcstage_key,rcstage_v,
                                rcstage_rc,rcstage_inst_id,rcstage_ccmd};

  assign sfifo_genbits_rrdy = ctr_drbg_gen_rdy_i && sfifo_genbits_rvld;
  assign {ctr_drbg_gen_fips_o,ctr_drbg_gen_bits_o,
          ctr_drbg_gen_key_o,ctr_drbg_gen_v_o,ctr_drbg_gen_rc_o,
          ctr_drbg_gen_inst_id_o,ctr_drbg_gen_ccmd_o} = sfifo_genbits_rdata;

  assign fifo_ggenbits_err_o =
        {( sfifo_genbits_wvld && !sfifo_genbits_wrdy),
         ( sfifo_genbits_rrdy && !sfifo_genbits_rvld),
         (!sfifo_genbits_wrdy && !sfifo_genbits_rvld)};

  // block ack
  assign ctr_drbg_gen_ack_o = sfifo_genbits_rrdy;

  // Return a status error when the genbits FIFO is popped while ctr_drbg_gen_ccmd_o is not
  // equal to GEN.
  assign ctr_drbg_gen_sts_err = sfifo_genbits_rrdy && (ctr_drbg_gen_ccmd_o != GENU);

  assign ctr_drbg_gen_sts_o = ctr_drbg_gen_sts_err ? CMD_STS_INVALID_GEN_CMD : CMD_STS_SUCCESS;

  // Make sure that the state machine has a stable error state. This means that after the error
  // state is entered it will not exit it unless a reset signal is received.
  `ASSERT(CsrngDrbgGenErrorStStable_A, state_q == ReqError |=> $stable(state_q))
  // If in error state, the error output must be high.
  `ASSERT(CsrngDrbgGenErrorOutput_A,
          !(state_q inside {ReqIdle, ReqSend, ESHalt}) |-> sm_err_o)

  // Unused signals
  logic [SeedLen-1:0] unused_upd_rsp_pdata;
  assign unused_upd_rsp_pdata = gen_upd_rsp_data_i.pdata;

endmodule
