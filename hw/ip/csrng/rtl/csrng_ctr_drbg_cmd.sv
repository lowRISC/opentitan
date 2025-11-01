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
  output logic               sm_err_o,
  output logic         [2:0] fifo_keyvrc_err_o
);

  localparam int KeyVRCFifoWidth  = CoreDataWidth + 1;

  // signals
  csrng_core_data_t   req_data;
  csrng_core_data_t   prep_core_data;
  csrng_core_data_t   keyvrc_data;
  logic               keyvrc_glast;

  logic [SeedLen-1:0] prep_seed_material;
  logic  [KeyLen-1:0] prep_key;
  logic  [BlkLen-1:0] prep_v;
  logic  [CtrLen-1:0] prep_rc;
  logic               bypass_upd;

  // keyvrc fifo
  logic                        sfifo_keyvrc_wvld;
  logic                        sfifo_keyvrc_wrdy;
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_wdata;
  logic                        sfifo_keyvrc_rvld;
  logic                        sfifo_keyvrc_rrdy;
  logic [KeyVRCFifoWidth-1:0]  sfifo_keyvrc_rdata;


  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 3 -n 5 \
  //     -s 68469135 --language=sv
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
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 3
  //
  localparam int StateWidth = 5;
  typedef enum logic [StateWidth-1:0] {
    ReqIdle = 5'b10000,
    RspPend = 5'b01010,
    Error   = 5'b00111
  } state_e;

  state_e state_d, state_q;

  // SEC_CM: UPDRSP.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, ReqIdle)


  //--------------------------------------------
  // Prepare/mux values for update step
  //--------------------------------------------

  always_comb begin
    req_data = req_data_i;
    // Insert the FIPS info from entropy source on instantiate and reseed commands.
    // Else, keep the existing info (from state db).
    req_data.fips = ((req_data_i.cmd == INS) || (req_data_i.cmd == RES)) ?
                      req_entropy_fips_i : req_data_i.fips;
  end

  assign prep_seed_material =
         (req_data.cmd == INS) ? (req_entropy_i ^ req_data.pdata) :
         (req_data.cmd == RES) ? (req_entropy_i ^ req_data.pdata) :
         (req_data.cmd == GEN) ? req_data.pdata :
         (req_data.cmd == UPD) ? req_data.pdata :
         '0;

  assign prep_key =
         (req_data.cmd == INS) ? '0 :
         (req_data.cmd == RES) ? req_data.key :
         (req_data.cmd == GEN) ? req_data.key :
         (req_data.cmd == UPD) ? req_data.key :
         '0;

  assign prep_v =
         (req_data.cmd == INS) ? '0 :
         (req_data.cmd == RES) ? req_data.v :
         (req_data.cmd == GEN) ? req_data.v :
         (req_data.cmd == UPD) ? req_data.v :
         '0;

  assign prep_rc =
         (req_data.cmd == INS) ? '0 :
         (req_data.cmd == RES) ? '0 :
         (req_data.cmd == GEN) ? req_data.rs_ctr :
         (req_data.cmd == UPD) ? req_data.rs_ctr :
         '0;

  // Request data for the update unit
  assign update_req_data_o = '{
    inst_id: req_data.inst_id,
    cmd:     req_data.cmd,
    key:     prep_key,
    v:       prep_v,
    pdata:   prep_seed_material
  };

  // Splice muxed data fields into internal data path
  always_comb begin
    prep_core_data = req_data;
    prep_core_data.key    = prep_key;
    prep_core_data.v      = prep_v;
    prep_core_data.rs_ctr = prep_rc;
  end

  // There are two cases in which we don't need the update unit:
  // 1) Generate commands with pdata equal to all-zero
  // 2) The (rather trivial) uninstantiate command
  assign bypass_upd = ((req_data.cmd == GEN) && (req_data.pdata == '0)) || (req_data.cmd == UNI);

  // Small FSM required to wait for a finished transaction on both the update unit
  // request and response ports until asserting the req_rdy_o to the upstream requester
  // in case the update unit is required.
  always_comb begin
    state_d = state_q;
    req_rdy_o = 1'b0;
    update_req_vld_o = 1'b0;
    update_rsp_rdy_o = 1'b0;
    sfifo_keyvrc_wvld = 1'b0;
    sm_err_o = 1'b0;

    unique case (state_q)
      ReqIdle: begin
        if (bypass_upd) begin
          req_rdy_o = enable_i && sfifo_keyvrc_wrdy;
          sfifo_keyvrc_wvld = req_vld_i;
        end else begin
          update_req_vld_o = req_vld_i;
          if (update_req_vld_o && update_req_rdy_i) begin
            state_d = RspPend;
          end
        end
      end
      RspPend: begin
        sfifo_keyvrc_wvld = update_rsp_vld_i;
        update_rsp_rdy_o  = sfifo_keyvrc_wrdy;
        if (update_rsp_vld_i && update_rsp_rdy_o) begin
          req_rdy_o = 1'b1;
          state_d = ReqIdle;
        end
      end
      Error: begin
        sm_err_o = 1'b1;
      end
      default: begin
        state_d = Error;
        sm_err_o = 1'b1;
      end
    endcase
  end


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

  // Route either data from request input or update response into keyvrc FIFO
  always_comb begin
    keyvrc_data  = prep_core_data;
    keyvrc_glast = req_glast_i;
    if (prep_core_data.cmd == UNI) begin
      // Zeroize everything but inst_id and cmd (?)
      keyvrc_data = '{default: '0};
      keyvrc_data.inst_id = prep_core_data.inst_id;
      keyvrc_data.cmd     = prep_core_data.cmd;
    end else if (!bypass_upd) begin
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
