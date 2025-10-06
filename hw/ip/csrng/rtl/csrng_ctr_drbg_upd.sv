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
  output logic       [2:0] fifo_final_err_o,
  output logic             sm_block_enc_req_err_o,
  output logic             sm_block_enc_rsp_err_o
);

  // signals
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
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 5 -n 6 \
  //     -s 47377994 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (50.00%)
  //  4: |||||||||||||||| (40.00%)
  //  5: |||| (10.00%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 5
  //

  localparam int BlkEncStateWidth = 6;
  typedef enum logic [BlkEncStateWidth-1:0] {
    ReqIdle = 6'b111011,
    ReqSend = 6'b000111,
    ReqWait = 6'b001010,
    ESHalt  = 6'b010100,
    BEError = 6'b101101
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
  // prepare value for block_encrypt step
  //--------------------------------------------

  // TODO(#28153) check if the (additional) increment here is really necessary and whether it
  // violates the redundant counter encoding listed as a SEC_CM below.
  if (CtrLen < BlkLen) begin : g_ctr_load_lsb
    logic [CtrLen-1:0] v_inc;
    assign v_inc  = req_data_i.v[CtrLen-1:0] + 1;
    assign v_load = {req_data_i.v[BlkLen-1:CtrLen], v_inc};
  end else begin : g_ctr_load_full
    assign v_load = req_data_i.v + 1;
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
    // Need to distinguish this case as the slice select into v_load above would otherwise yield an
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
    block_encrypt_req_vld_o = 1'b0;
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
        end else if (req_vld_i) begin
          v_ctr_load = 1'b1;
          blk_enc_state_d = ReqSend;
        end
      end
      ReqSend: begin
        if (!enable_i) begin
          blk_enc_state_d = ReqIdle;
        end else if (!block_ctr_done) begin
          block_encrypt_req_vld_o = 1'b1;
          if (block_encrypt_req_rdy_i) begin
            v_ctr_inc  = 1'b1;
          end
        end else begin
          // Wait for completion on the benc_rsp path
          if (req_vld_i && req_rdy_o) begin
            blk_enc_state_d = ReqIdle;
          end else begin
            blk_enc_state_d = ReqWait;
          end
        end
      end
      ReqWait: begin
        if (!enable_i) begin
          blk_enc_state_d = ReqIdle;
        end else if (req_vld_i && req_rdy_o) begin
          // Wait for completion on the benc_rsp path
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

  // Forward the upstream data together with the current counter value to block_encrypt
  assign block_encrypt_req_data_o = {req_data_i.inst_id,
                                     req_data_i.cmd,
                                     req_data_i.key,
                                     v_ctr_sized};

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
    end else if (block_encrypt_rsp_vld_i && block_encrypt_rsp_rdy_o) begin
      concat_inst_id_d = block_encrypt_rsp_data_i.inst_id;
      concat_ccmd_d    = block_encrypt_rsp_data_i.cmd;
      // Replace LSBs of shift value with data from block_encrypt
      concat_outblk_d  = {concat_outblk_q[SeedLen-1:BlkLen],
                          block_encrypt_rsp_data_i.v};
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
    block_encrypt_rsp_rdy_o = 1'b0;
    sfifo_final_wvld = 1'b0;
    req_rdy_o = 1'b0;
    sm_block_enc_rsp_err_o = 1'b0;
    unique case (outblk_state_q)
      // AckIdle: increment v this cycle, push in next
      AckIdle: begin
        if (!enable_i) begin
          // There is no "clear" on the AES cipher, so just flush out any outstanding responses
          // Otherwise, there will be erroneous handshakes when re-enabling the CSRNG
          block_encrypt_rsp_rdy_o = 1'b1;
          outblk_state_d = AckIdle;
        end else if (sfifo_final_wrdy) begin
          outblk_state_d = Load;
        end
      end
      Load: begin
        if (!enable_i) begin
          outblk_state_d = AckIdle;
        end else begin
          block_encrypt_rsp_rdy_o = 1'b1;
          if (block_encrypt_rsp_vld_i) begin
            concat_ctr_inc = 1'b1;
            outblk_state_d = Shift;
          end
        end
      end
      Shift: begin
        if (!enable_i) begin
          outblk_state_d = AckIdle;
        end else if (concat_ctr_done) begin
          req_rdy_o = 1'b1;
          sfifo_final_wvld  = 1'b1;
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
  assign updated_key_and_v = concat_outblk_q ^ req_data_i.pdata;

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
  logic [KeyLen-1:0] unused_block_encrypt_rsp_data_key;
  assign unused_block_encrypt_rsp_data_key = block_encrypt_rsp_data_i.key;

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
