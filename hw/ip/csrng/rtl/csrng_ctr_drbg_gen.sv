// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng ctr_drbg generate module
//
// This module will process the second half of the generate function.
// It takes in the key, v, and reseed counter values processed by the
// ctr_drbg_cmd module.

`include "prim_assert.sv"

module csrng_ctr_drbg_gen import csrng_pkg::*; (
  input  logic              clk_i,
  input  logic              rst_ni,

  // Global enable
  input  logic              enable_i,

  // Command interface request from cmd stage
  input  logic              cmd_req_vld_i,
  output logic              cmd_req_rdy_o,
  input  csrng_core_data_t  cmd_req_data_i,
  input  logic              cmd_req_glast_i,

  // Command interface response to state db
  output logic              cmd_rsp_vld_o,
  input  logic              cmd_rsp_rdy_i,
  output csrng_core_data_t  cmd_rsp_data_o,
  output logic [BlkLen-1:0] cmd_rsp_bits_o,
  output csrng_cmd_sts_e    cmd_rsp_sts_o,

  // Halt request from entropy source
  input  logic              es_halt_req_i,
  output logic              es_halt_ack_o,

  // Update interface request
  output logic              update_req_vld_o,
  input  logic              update_req_rdy_i,
  output csrng_upd_data_t   update_req_data_o,

  // Update interface response
  input  logic              update_rsp_vld_i,
  output logic              update_rsp_rdy_o,
  input  csrng_upd_data_t   update_rsp_data_i,

  // Block encrypt interface request
  output logic              block_encrypt_req_vld_o,
  input  logic              block_encrypt_req_rdy_i,
  output csrng_benc_data_t  block_encrypt_req_data_o,

  // Block encrypt interface response
  input  logic              block_encrypt_rsp_vld_i,
  output logic              block_encrypt_rsp_rdy_o,
  input  csrng_benc_data_t  block_encrypt_rsp_data_i,

  // Error status signals
  output logic              ctr_err_o,
  output logic              sm_err_o,
  output logic        [2:0] fifo_gbencack_err_o,
  output logic        [2:0] fifo_gadstage_err_o
);

  import csrng_reg_pkg::NumApps;

  // FIFO widths. All are 1-element deep.
  // Note: Often, the full width is not utilized but only declared to be able to
  // convienently make use of common struct data types for read- and write data.
  localparam int AdstageFifoWidth = KeyLen + BlkLen + CtrLen + 2;

  // FIFO signals. Two stages in total
  logic                        sfifo_adstage_wvld;
  logic                        sfifo_adstage_wrdy;
  logic [AdstageFifoWidth-1:0] sfifo_adstage_wdata;
  logic                        sfifo_adstage_rvld;
  logic                        sfifo_adstage_rrdy;
  logic [AdstageFifoWidth-1:0] sfifo_adstage_rdata;

  logic                        sfifo_bencack_wvld;
  logic                        sfifo_bencack_wrdy;
  csrng_benc_data_t            sfifo_bencack_wdata;
  logic                        sfifo_bencack_rvld;
  logic                        sfifo_bencack_rrdy;
  csrng_benc_data_t            sfifo_bencack_rdata;

  // Helper/breakout signals between the FIFO stages
  logic  [KeyLen-1:0] adstage_key;
  logic  [BlkLen-1:0] adstage_v;
  logic  [CtrLen-1:0] adstage_rs_ctr;
  logic               adstage_fips;
  logic               adstage_glast;

  // Control and data signals, mostly for the v counter
  logic  [BlkLen-1:0] v_load;
  logic  [BlkLen-1:0] v_ctr_sized;
  logic               v_ctr_load;
  logic               v_ctr_inc;
  logic  [CtrLen-1:0] v_ctr;
  logic [NumApps-1:0] capt_adata;

  // adata flops for each app interface, plus one valid bit for each
  logic [SeedLen-1:0] update_adata_q[NumApps], update_adata_d[NumApps];
  logic [NumApps-1:0] update_adata_vld_q, update_adata_vld_d;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 7 -n 6 \
  //     -s 12450626389 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 3
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    ReqIdle     = 6'b010101,
    ReqSend     = 6'b111000,
    ESHalt      = 6'b010010,
    ReqError    = 6'b100100,
    BencRspWait = 6'b100011,
    UpdRspWait  = 6'b001110,
    UpdESHalt   = 6'b001001
  } state_e;

  state_e state_d, state_q;

  // SEC_CM: UPDATE.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, ReqIdle)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      update_adata_q     <= '{default:0};
      update_adata_vld_q <= '0;
    end else begin
      update_adata_q     <= update_adata_d;
      update_adata_vld_q <= update_adata_vld_d;
    end
  end


  //--------------------------------------------
  // prepare value for block_encrypt step
  //--------------------------------------------

  // TODO(#28153) check if the (additional) increment here is really necessary and whether it
  // violates the redundant counter encoding listed as a SEC_CM below.
  if (CtrLen < BlkLen) begin : g_ctr_load_lsb
    logic [CtrLen-1:0] v_inc;
    assign v_inc  = cmd_req_data_i.v[CtrLen-1:0] + 1;
    assign v_load = {cmd_req_data_i.v[BlkLen-1:CtrLen], v_inc};
  end else begin : g_ctr_load_full
    assign v_load = cmd_req_data_i.v + 1;
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
  // state machine to control conditional requests/responses to/from update unit
  //--------------------------------------------

  // Send genreq data with the altered v, and change the command code
  // to an internal one for proper routing in csrng_core
  assign block_encrypt_req_data_o = '{
    inst_id: cmd_req_data_i.inst_id,
    cmd:     (cmd_req_data_i.cmd == GEN) ? GENB : INV,
    key:     cmd_req_data_i.key,
    v:       v_ctr_sized
  };

  assign update_rsp_rdy_o = cmd_rsp_rdy_i;

  always_comb begin
    state_d = state_q;
    v_ctr_load = 1'b0;
    v_ctr_inc  = 1'b0;
    sfifo_adstage_wvld = 1'b0;
    sfifo_bencack_rrdy = 1'b0;
    sfifo_adstage_rrdy = 1'b0;
    cmd_req_rdy_o = 1'b0;
    cmd_rsp_vld_o = 1'b0;
    block_encrypt_req_vld_o = 1'b0;
    update_req_vld_o = 1'b0;
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
        end else if (cmd_req_vld_i && sfifo_adstage_wrdy) begin
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
            cmd_req_rdy_o = 1'b1;
            // Increment v & back to idle
            v_ctr_inc = 1'b1;
            state_d   = BencRspWait;
          end
        end
      end
      BencRspWait: begin
        if (!enable_i) begin
          state_d = ReqIdle;
        end else if (sfifo_bencack_rvld) begin
          if (adstage_glast) begin
            update_req_vld_o = 1'b1;
            // Wait for update unit
            if (update_req_rdy_i) begin
              state_d = UpdRspWait;
            end
            // Abort the process in case of a halt request, as the
            // update unit won't answer them until the halt ack
            if (es_halt_req_i) begin
              state_d = UpdESHalt;
            end
          end else begin
            cmd_rsp_vld_o = 1'b1;
            if (cmd_rsp_rdy_i) begin
              sfifo_bencack_rrdy = 1'b1;
              sfifo_adstage_rrdy = 1'b1;
              state_d = ReqIdle;
            end
          end
        end
      end
      UpdRspWait: begin
        if (!enable_i) begin
          state_d = ReqIdle;
        end else if (update_rsp_vld_i) begin
          cmd_rsp_vld_o = 1'b1;
          if (cmd_rsp_rdy_i) begin
            sfifo_bencack_rrdy = 1'b1;
            sfifo_adstage_rrdy = 1'b1;
            state_d = ReqIdle;
          end
        end
      end
      ESHalt: begin
        es_halt_ack_o = 1'b1;
        if (!es_halt_req_i) begin
          state_d = ReqIdle;
        end
      end
      UpdESHalt: begin
        es_halt_ack_o = 1'b1;
        // We have to keep the update_req_vld high, else we get
        // the arbiter asserts firing
        update_req_vld_o = 1'b1;
        if (!es_halt_req_i) begin
          state_d = BencRspWait;
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
  // fifo to stage key, v, rs_ctr, and adata, waiting for update block to ack
  //--------------------------------------------

  prim_fifo_sync #(
    .Width(AdstageFifoWidth),
    .Pass(0),
    .Depth(1),
    .OutputZeroIfEmpty(1'b0)
  ) u_prim_fifo_sync_adstage (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .clr_i   (!enable_i),
    .wvalid_i(sfifo_adstage_wvld),
    .wready_o(sfifo_adstage_wrdy),
    .wdata_i (sfifo_adstage_wdata),
    .rvalid_o(sfifo_adstage_rvld),
    .rready_i(sfifo_adstage_rrdy),
    .rdata_o (sfifo_adstage_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  assign sfifo_adstage_wdata = {cmd_req_glast_i,
                                cmd_req_data_i.key,
                                v_ctr_sized,
                                cmd_req_data_i.rs_ctr,
                                cmd_req_data_i.fips};

  assign {adstage_glast,
          adstage_key,
          adstage_v,
          adstage_rs_ctr,
          adstage_fips} = sfifo_adstage_rdata;

  assign fifo_gadstage_err_o =
         {( sfifo_adstage_wvld && !sfifo_adstage_wrdy),
          ( sfifo_adstage_rrdy && !sfifo_adstage_rvld),
          (!sfifo_adstage_wrdy && !sfifo_adstage_rvld)};


  // adata storage for each application interface:
  // - Write from genreq stage if not currently valid
  // - Clear valid upon sending request to update unit (== last generate beat done)
  for (genvar i = 0; i < NumApps; i++) begin : gen_adata
    assign capt_adata[i] = (sfifo_adstage_wvld && (cmd_req_data_i.inst_id == i));

    always_comb begin
      update_adata_vld_d[i] = update_adata_vld_q[i];
      update_adata_d[i]     = update_adata_q[i];

      if (!enable_i) begin
        update_adata_vld_d[i] = 1'b0;
        update_adata_d[i]     = '0;
      end else if (capt_adata[i] && !update_adata_vld_q[i]) begin
        update_adata_vld_d[i] = 1'b1;
        update_adata_d[i]     = cmd_req_data_i.pdata;
      end else if (update_req_vld_o && update_req_rdy_i && (sfifo_bencack_rdata.inst_id == i)) begin
        update_adata_vld_d[i] = 1'b0;
      end
    end
  end

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

  always_comb begin
    sfifo_bencack_wdata = block_encrypt_rsp_data_i;
    sfifo_bencack_wdata.cmd = (block_encrypt_rsp_data_i.cmd == GENB) ? GENU : INV;
  end

  assign sfifo_bencack_wvld  = sfifo_bencack_wrdy && block_encrypt_rsp_vld_i;

  assign block_encrypt_rsp_rdy_o = sfifo_bencack_wrdy;

  assign fifo_gbencack_err_o =
         {( sfifo_bencack_wvld && !sfifo_bencack_wrdy),
          ( sfifo_bencack_rrdy && !sfifo_bencack_rvld),
          (!sfifo_bencack_wrdy && !sfifo_bencack_rvld)};


  //--------------------------------------------
  // prepare values for update step
  //--------------------------------------------

  assign update_req_data_o = '{
    inst_id: sfifo_bencack_rdata.inst_id,
    cmd:     sfifo_bencack_rdata.cmd,
    key:     adstage_key,
    v:       adstage_v,
    pdata:   update_adata_q[sfifo_bencack_rdata.inst_id[NumAppsLg-1:0]]
  };

  //--------------------------------------------
  // Mux results of update unit to output on last beat
  //--------------------------------------------

  always_comb begin
    cmd_rsp_data_o = '{
      inst_id: sfifo_bencack_rdata.inst_id,
      cmd:     sfifo_bencack_rdata.cmd,
      key:     adstage_key,
      v:       adstage_v,
      pdata:   '0, // unused
      rs_ctr:  adstage_rs_ctr,
      fips:    adstage_fips
    };

    // On the last gen beat, splice in the updated key & v values from the
    // update unit, and increase the reseed counter by one.
    if (adstage_glast) begin
      cmd_rsp_data_o.inst_id = update_rsp_data_i.inst_id;
      cmd_rsp_data_o.cmd     = update_rsp_data_i.cmd;
      cmd_rsp_data_o.key     = update_rsp_data_i.key;
      cmd_rsp_data_o.v       = update_rsp_data_i.v;
      cmd_rsp_data_o.rs_ctr  = adstage_rs_ctr + 1;
    end
  end

  assign cmd_rsp_bits_o = sfifo_bencack_rdata.v;
  assign cmd_rsp_sts_o  = (cmd_rsp_vld_o && (cmd_rsp_data_o.cmd != GENU)) ? CMD_STS_INVALID_GEN_CMD
                                                                          : CMD_STS_SUCCESS;

  // Make sure that the state machine has a stable error state. This means that after the error
  // state is entered it will not exit it unless a reset signal is received.
  `ASSERT(CsrngDrbgGenErrorStStable_A, state_q == ReqError |=> $stable(state_q))
  // If in error state, the error output must be high.
  `ASSERT(CsrngDrbgGenErrorOutput_A,
          !(state_q inside {ReqIdle, ReqSend, ESHalt, BencRspWait, UpdRspWait, UpdESHalt})
          |-> sm_err_o)

  // Unused signals
  logic [SeedLen-1:0] unused_upd_rsp_pdata;
  logic  [KeyLen-1:0] unused_bencack_sfifo_rdata_key;
  assign unused_upd_rsp_pdata = update_rsp_data_i.pdata;
  assign unused_bencack_sfifo_rdata_key = sfifo_bencack_rdata.key;

endmodule
