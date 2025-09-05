// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng ctr_drbg_update module
//
// implementation using security_strength = 256

`include "prim_assert.sv"

module csrng_ctr_drbg_upd import csrng_pkg::*; (
  input  logic             clk_i,
  input  logic             rst_ni,

  // Global enable
  input  logic             enable_i,

  // Update interface request from cmd and generate stages
  input  logic             req_vld_i,
  output logic             req_rdy_o,
  input  csrng_upd_data_t  req_data_i,

  // Update interface response to cmd and generate stages
  output logic             rsp_vld_o,
  input  logic             rsp_rdy_i,
  output csrng_upd_data_t  rsp_data_o,

  // Halt request from entropy source
  input  logic             es_halt_req_i,
  output logic             es_halt_ack_o,

  // Block encrypt interface request
  output logic             block_encrypt_req_vld_o,
  input  logic             block_encrypt_req_rdy_i,
  output csrng_benc_data_t block_encrypt_req_data_o,

  // Block encrypt interface response
  input  logic             block_encrypt_rsp_vld_i,
  output logic             block_encrypt_rsp_rdy_o,
  input  csrng_benc_data_t block_encrypt_rsp_data_i,

  // Error status outputs
  output logic             ctr_err_o,
  output logic       [2:0] fifo_updreq_err_o,
  output logic       [2:0] fifo_bencreq_err_o,
  output logic       [2:0] fifo_bencack_err_o,
  output logic       [2:0] fifo_pdata_err_o,
  output logic       [2:0] fifo_final_err_o,
  output logic             sm_block_enc_req_err_o,
  output logic             sm_block_enc_rsp_err_o
);

  // signals
  // updreq fifo
  logic                     sfifo_updreq_wvld;
  logic                     sfifo_updreq_wrdy;
  logic  [UpdDataWidth-1:0] sfifo_updreq_wdata;
  logic                     sfifo_updreq_rvld;
  logic                     sfifo_updreq_rrdy;
  logic  [UpdDataWidth-1:0] sfifo_updreq_rdata;

  csrng_upd_data_t          req_data_fifo;

  // blk_encrypt_req fifo
  logic                     sfifo_bencreq_wvld;
  logic                     sfifo_bencreq_wrdy;
  logic [BencDataWidth-1:0] sfifo_bencreq_rdata;
  logic                     sfifo_bencreq_rvld;
  logic                     sfifo_bencreq_rrdy;
  logic [BencDataWidth-1:0] sfifo_bencreq_wdata;

  // blk_encrypt_ack fifo
  logic                     sfifo_bencack_wvld;
  logic                     sfifo_bencack_wrdy;
  logic [BencDataWidth-1:0] sfifo_bencack_wdata;
  logic                     sfifo_bencack_rvld;
  logic                     sfifo_bencack_rrdy;
  logic [BencDataWidth-1:0] sfifo_bencack_rdata;

  csrng_benc_data_t         benc_rsp_data_fifo;

  // pdata_stage fifo
  logic                     sfifo_pdata_wvld;
  logic                     sfifo_pdata_wrdy;
  logic       [SeedLen-1:0] sfifo_pdata_wdata;
  logic                     sfifo_pdata_rvld;
  logic                     sfifo_pdata_rrdy;
  logic       [SeedLen-1:0] sfifo_pdata_rdata;

  // key_v fifo
  logic                     sfifo_final_wvld;
  logic                     sfifo_final_wrdy;
  logic [BencDataWidth-1:0] sfifo_final_wdata;
  logic                     sfifo_final_rvld;
  logic                     sfifo_final_rrdy;
  logic [BencDataWidth-1:0] sfifo_final_rdata;

  logic                     v_ctr_load;
  logic                     v_ctr_inc;
  logic                     block_ctr_done;
  logic                     concat_outblk_shift;
  logic                     concat_ctr_done;
  logic                     concat_ctr_inc;
  logic        [CtrLen-1:0] v_ctr;

  logic       [SeedLen-1:0] updated_key_and_v;
  logic        [BlkLen-1:0] v_load;
  logic        [BlkLen-1:0] v_ctr_sized;

  // flops
  logic             [1:0] block_ctr_q, block_ctr_d;
  logic             [1:0] concat_ctr_q, concat_ctr_d;
  logic     [SeedLen-1:0] concat_outblk_q, concat_outblk_d;
  logic    [CmdWidth-1:0] concat_ccmd_q, concat_ccmd_d;
  logic [InstIdWidth-1:0] concat_inst_id_q, concat_inst_id_d;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 4 -n 5 \
  //      -s 47328894 --language=sv
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

  localparam int BlkEncStateWidth = 5;
  typedef enum logic [BlkEncStateWidth-1:0] {
    ReqIdle = 5'b11000,
    ReqSend = 5'b10011,
    ESHalt  = 5'b01110,
    BEError = 5'b00101
  } blk_enc_state_e;

  blk_enc_state_e blk_enc_state_d, blk_enc_state_q;

  // SEC_CM: BLK_ENC.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_blk_enc_state_regs, blk_enc_state_d, blk_enc_state_q, blk_enc_state_e,
                        ReqIdle)

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 4 -n 6 \
  //      -s 400877681 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (66.67%)
  //  4: ||||| (16.67%)
  //  5: --
  //  6: ||||| (16.67%)
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 4
  //

  localparam int OutBlkStateWidth = 6;
  typedef enum logic [OutBlkStateWidth-1:0] {
    AckIdle = 6'b110110,
    Load    = 6'b110001,
    Shift   = 6'b001001,
    OBError = 6'b011100
  } outblk_state_e;

  outblk_state_e outblk_state_d, outblk_state_q;

  // SEC_CM: OUTBLK.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_outblk_state_regs,
                        outblk_state_d, outblk_state_q, outblk_state_e, AckIdle)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      block_ctr_q      <= '0;
      concat_ctr_q     <= '0;
      concat_outblk_q  <= '0;
      concat_ccmd_q    <= '0;
      concat_inst_id_q <= '0;
    end else begin
      block_ctr_q      <= block_ctr_d;
      concat_ctr_q     <= concat_ctr_d;
      concat_outblk_q  <= concat_outblk_d;
      concat_ccmd_q    <= concat_ccmd_d;
      concat_inst_id_q <= concat_inst_id_d;
    end
  end

  //--------------------------------------------
  // input request fifo for staging update requests
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(UpdDataWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_updreq (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_updreq_wvld),
    .wready_o(sfifo_updreq_wrdy),
    .wdata_i (sfifo_updreq_wdata),
    .rvalid_o(sfifo_updreq_rvld),
    .rready_i(sfifo_updreq_rrdy),
    .rdata_o (sfifo_updreq_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  assign sfifo_updreq_wvld  = sfifo_updreq_wrdy && req_vld_i;
  assign sfifo_updreq_wdata = req_data_i;
  assign req_rdy_o          = sfifo_updreq_wrdy;

  assign req_data_fifo = sfifo_updreq_rdata;

  assign fifo_updreq_err_o = {
         ( sfifo_updreq_wvld && !sfifo_updreq_wrdy),
         ( sfifo_updreq_rrdy && !sfifo_updreq_rvld),
         (!sfifo_updreq_wrdy && !sfifo_updreq_rvld)};

  //--------------------------------------------
  // prepare value for block_encrypt step
  //--------------------------------------------

  // TODO(#28153) check if the (additional) increment here is really necessary and whether it
  // violates the redundant counter encoding listed as a SEC_CM below.
  if (CtrLen < BlkLen) begin : g_ctr_load_lsb
    logic [CtrLen-1:0] v_inc;
    assign v_inc  = req_data_fifo.v[CtrLen-1:0] + 1;
    assign v_load = {req_data_fifo.v[BlkLen-1:CtrLen], v_inc};
  end else begin : g_ctr_load_full
    assign v_load = req_data_fifo.v + 1;
  end

  // SEC_CM: DRBG_UPD.CTR.REDUN
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
    // Need to distinguish this case as the slice select above into v_load above would yield an
    // incorrect range ([BlkLen-1:BlkLen])
    assign v_ctr_sized = v_ctr;
  end

  // Count the number of blocks that have been sent to block_encrypt for each call of the update
  // function, until blocks adding to at least SeedLen bits have been sent.
  // Counting up is done in sync with the 'main' v counter above
  always_comb begin
    block_ctr_d = block_ctr_q;
    if (!enable_i) begin
      block_ctr_d = '0;
    end else if (block_ctr_done) begin
      block_ctr_d = '0;
    end else if (v_ctr_inc) begin
      block_ctr_d = block_ctr_q + 1;
    end
  end

  // Doing this inside the always_comb above results in some simulator tools getting stuck at the
  // beginning of the simulation.
  assign block_ctr_done = (block_ctr_q >= SeedLen/BlkLen);

  //--------------------------------------------
  // state machine to send values to block_encrypt
  //--------------------------------------------

  always_comb begin
    blk_enc_state_d = blk_enc_state_q;
    v_ctr_load = 1'b0;
    v_ctr_inc  = 1'b0;
    sfifo_pdata_wvld = 1'b0;
    sfifo_bencreq_wvld = 1'b0;
    sfifo_updreq_rrdy = 1'b0;
    sm_block_enc_req_err_o = 1'b0;
    es_halt_ack_o = 1'b0;
    unique case (blk_enc_state_q)
      // ReqIdle: increment v this cycle, push in next
      ReqIdle: begin
        // Prioritize halt requests from entropy_src over disable, as CSRNG would otherwise starve
        // those requests while it is idle.
        if (es_halt_req_i) begin
          blk_enc_state_d = ESHalt;
        end else if (!enable_i) begin
          blk_enc_state_d = ReqIdle;
        end else if (sfifo_updreq_rvld && sfifo_bencreq_wrdy && sfifo_pdata_wrdy) begin
          v_ctr_load = 1'b1;
          sfifo_pdata_wvld = 1'b1;
          blk_enc_state_d = ReqSend;
        end
      end
      ReqSend: begin
        if (!enable_i) begin
          blk_enc_state_d = ReqIdle;
        end else if (!block_ctr_done) begin
          if (sfifo_bencreq_wrdy) begin
            v_ctr_inc  = 1'b1;
            sfifo_bencreq_wvld = 1'b1;
          end
        end else begin
          sfifo_updreq_rrdy = 1'b1;
          blk_enc_state_d = ReqIdle;
        end
      end
      ESHalt: begin
        es_halt_ack_o = 1'b1;
        if (!es_halt_req_i) begin
          blk_enc_state_d = ReqIdle;
        end
      end
      BEError: begin
        sm_block_enc_req_err_o = 1'b1;
      end
      default: begin
        blk_enc_state_d = BEError;
        sm_block_enc_req_err_o = 1'b1;
      end
    endcase
  end

  //--------------------------------------------
  // block_encrypt request fifo for staging aes requests
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(BencDataWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_bencreq (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_bencreq_wvld),
    .wready_o(sfifo_bencreq_wrdy),
    .wdata_i (sfifo_bencreq_wdata),
    .rvalid_o(sfifo_bencreq_rvld),
    .rready_i(sfifo_bencreq_rrdy),
    .rdata_o (sfifo_bencreq_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  assign sfifo_bencreq_rrdy = sfifo_bencreq_rvld && block_encrypt_req_rdy_i;
  assign block_encrypt_req_vld_o = sfifo_bencreq_rvld;

  // Forward the upstream data together with the current counter value to block_encrypt
  assign sfifo_bencreq_wdata = {req_data_fifo.inst_id,
                                req_data_fifo.cmd,
                                req_data_fifo.key,
                                v_ctr_sized};

  // rdata of the FIFO is already in the correct format
  assign block_encrypt_req_data_o = sfifo_bencreq_rdata;

  assign fifo_bencreq_err_o =
         {( sfifo_bencreq_wvld && !sfifo_bencreq_wrdy),
          ( sfifo_bencreq_rrdy && !sfifo_bencreq_rvld),
          (!sfifo_bencreq_wrdy && !sfifo_bencreq_rvld)};

  //--------------------------------------------
  // block_encrypt response fifo from block encrypt
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(BencDataWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_bencack (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_bencack_wvld),
    .wready_o(sfifo_bencack_wrdy),
    .wdata_i (sfifo_bencack_wdata),
    .rvalid_o(sfifo_bencack_rvld),
    .rready_i(sfifo_bencack_rrdy),
    .rdata_o (sfifo_bencack_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  assign sfifo_bencack_wvld  = block_encrypt_rsp_vld_i && sfifo_bencack_wrdy;
  assign sfifo_bencack_wdata = block_encrypt_rsp_data_i;
  assign block_encrypt_rsp_rdy_o = sfifo_bencack_wrdy;

  assign benc_rsp_data_fifo = sfifo_bencack_rdata;

  assign fifo_bencack_err_o =
         {( sfifo_bencack_wvld && !sfifo_bencack_wrdy),
          ( sfifo_bencack_rrdy && !sfifo_bencack_rvld),
          (!sfifo_bencack_wrdy && !sfifo_bencack_rvld)};

  //--------------------------------------------
  // fifo to stage provided_data, waiting for blk_encrypt to ack
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(SeedLen),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_pdata (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_pdata_wvld),
    .wready_o(sfifo_pdata_wrdy),
    .wdata_i (sfifo_pdata_wdata),
    .rvalid_o(sfifo_pdata_rvld),
    .rready_i(sfifo_pdata_rrdy),
    .rdata_o (sfifo_pdata_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  assign sfifo_pdata_wdata = req_data_fifo.pdata;

  assign fifo_pdata_err_o =
         {( sfifo_pdata_wvld && !sfifo_pdata_wrdy),
          ( sfifo_pdata_rrdy && !sfifo_pdata_rvld),
          (!sfifo_pdata_wrdy && !sfifo_pdata_rvld)};

  //--------------------------------------------
  // shifting logic to receive values from block_encrypt
  //--------------------------------------------

  always_comb begin
    concat_inst_id_d = concat_inst_id_q;
    concat_ccmd_d    = concat_ccmd_q;
    concat_outblk_d  = concat_outblk_q;
    if (!enable_i) begin
      concat_inst_id_d = '0;
      concat_ccmd_d    = '0;
      concat_outblk_d  = '0;
    end else if (sfifo_bencack_rrdy) begin
      concat_inst_id_d = benc_rsp_data_fifo.inst_id;
      concat_ccmd_d    = benc_rsp_data_fifo.cmd;
      // Replace LSBs of shift value with data from block_encrypt
      concat_outblk_d  = {concat_outblk_q[SeedLen-1:BlkLen],
                          benc_rsp_data_fifo.v};
    end else if (concat_outblk_shift) begin
      // Shift value left by BlkLen bits
      concat_outblk_d  = {concat_outblk_q[SeedLen-BlkLen-1:0], {BlkLen{1'b0}}};
    end
  end

  // Count the number of blocks that have been received back from block_encrypt until enough blocks
  // have been received for at least SeedLen bits in total.
  always_comb begin
    concat_ctr_d = concat_ctr_q;
    if (!enable_i) begin
      concat_ctr_d = '0;
    end else if (concat_ctr_done) begin
      concat_ctr_d = '0;
    end else if (concat_ctr_inc) begin
      concat_ctr_d = concat_ctr_q + 1;
    end
  end

  assign concat_ctr_done = (concat_ctr_q >= SeedLen/BlkLen);

  //--------------------------------------------
  // state machine to receive values from block_encrypt
  //--------------------------------------------

  always_comb begin
    outblk_state_d = outblk_state_q;
    concat_ctr_inc  = 1'b0;
    concat_outblk_shift = 1'b0;
    sfifo_pdata_rrdy = 1'b0;
    sfifo_bencack_rrdy = 1'b0;
    sfifo_final_wvld = 1'b0;
    sm_block_enc_rsp_err_o = 1'b0;
    unique case (outblk_state_q)
      // AckIdle: increment v this cycle, push in next
      AckIdle: begin
        if (!enable_i) begin
          outblk_state_d = AckIdle;
        end else if (sfifo_bencack_rvld && sfifo_pdata_rvld && sfifo_final_wrdy) begin
          outblk_state_d = Load;
        end
      end
      Load: begin
        if (!enable_i) begin
          outblk_state_d = AckIdle;
        end else if (sfifo_bencack_rvld) begin
          concat_ctr_inc  = 1'b1;
          sfifo_bencack_rrdy = 1'b1;
          outblk_state_d = Shift;
        end
      end
      Shift: begin
        if (!enable_i) begin
          outblk_state_d = AckIdle;
        end else if (concat_ctr_done) begin
          sfifo_pdata_rrdy = 1'b1;
          sfifo_final_wvld = 1'b1;
          outblk_state_d = AckIdle;
        end else begin
          concat_outblk_shift = 1'b1;
          outblk_state_d = Load;
        end
      end
      OBError: begin
        sm_block_enc_rsp_err_o = 1'b1;
      end
      default: begin
        outblk_state_d = OBError;
        sm_block_enc_rsp_err_o = 1'b1;
      end
    endcase
  end


  //--------------------------------------------
  // final update processing
  //--------------------------------------------

  // XOR the additional data with the new key and value from block encryption
  assign updated_key_and_v = concat_outblk_q ^ sfifo_pdata_rdata;

  prim_fifo_sync #(
    .Width(BencDataWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_final (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_final_wvld),
    .wready_o(sfifo_final_wrdy),
    .wdata_i (sfifo_final_wdata),
    .rvalid_o(sfifo_final_rvld),
    .rready_i(sfifo_final_rrdy),
    .rdata_o (sfifo_final_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  assign sfifo_final_wdata = {concat_inst_id_q,
                              concat_ccmd_q,
                              updated_key_and_v};

  assign sfifo_final_rrdy = rsp_rdy_i && sfifo_final_rvld;
  assign rsp_vld_o  = sfifo_final_rrdy;
  // pdata (in the MSBs) is unused in rsp path
  assign rsp_data_o = csrng_upd_data_t'({{SeedLen{1'b0}}, sfifo_final_rdata});

  assign fifo_final_err_o =
         {( sfifo_final_wvld && !sfifo_final_wrdy),
          ( sfifo_final_rrdy && !sfifo_final_rvld),
          (!sfifo_final_wrdy && !sfifo_final_rvld)};

  // Unused signals
  logic [KeyLen-1:0] unused_benc_rsp_data_fifo_key;
  assign unused_benc_rsp_data_fifo_key = benc_rsp_data_fifo.key;

  // Make sure that the two state machines have a stable error state. This means that after the
  // error state is entered it will not exit it unless a reset signal is received.
  `ASSERT(CsrngDrbgUpdBlkEncErrorStStable_A,
          blk_enc_state_q == BEError |=> $stable(blk_enc_state_q))
  `ASSERT(CsrngDrbgUpdOutBlkErrorStStable_A,
          outblk_state_q  == OBError |=> $stable(outblk_state_q))

  // If in error state, the error output must be high.
  `ASSERT(CsrngDrbgUpdBlkEncErrorOutput_A, blk_enc_state_q == BEError |-> sm_block_enc_req_err_o)
  `ASSERT(CsrngDrbgUpdOutBlkErrorOutput_A, outblk_state_q  == OBError |-> sm_block_enc_rsp_err_o)
endmodule
