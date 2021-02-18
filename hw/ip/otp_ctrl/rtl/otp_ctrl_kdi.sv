// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Scrambling key derivation module for OTP.
//

`include "prim_assert.sv"

module otp_ctrl_kdi
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
(
  input                                              clk_i,
  input                                              rst_ni,
  // Pulse to enable this module after OTP partitions have
  // been initialized.
  input                                              kdi_en_i,
  // Escalation input. This moves the FSM into a terminal state.
  input  lc_ctrl_pkg::lc_tx_t                        escalate_en_i,
  // FSM is in error state
  output logic                                       fsm_err_o,
  // Key seed inputs from OTP
  input  logic                                       scrmbl_key_seed_valid_i,
  input  logic [FlashKeySeedWidth-1:0]               flash_data_key_seed_i,
  input  logic [FlashKeySeedWidth-1:0]               flash_addr_key_seed_i,
  input  logic [SramKeySeedWidth-1:0]                sram_data_key_seed_i,
  // EDN interface for requesting entropy
  output logic                                       edn_req_o,
  input                                              edn_ack_i,
  input  [EdnDataWidth-1:0]                          edn_data_i,
  // Lifecycle hashing request
  input  lc_otp_token_req_t                          lc_otp_token_i,
  output lc_otp_token_rsp_t                          lc_otp_token_o,
  // Scrambling key requests
  input  flash_otp_key_req_t                         flash_otp_key_i,
  output flash_otp_key_rsp_t                         flash_otp_key_o,
  input  sram_otp_key_req_t [NumSramKeyReqSlots-1:0] sram_otp_key_i,
  output sram_otp_key_rsp_t [NumSramKeyReqSlots-1:0] sram_otp_key_o,
  input  otbn_otp_key_req_t                          otbn_otp_key_i,
  output otbn_otp_key_rsp_t                          otbn_otp_key_o,
  // Scrambling mutex request
  output logic                                       scrmbl_mtx_req_o,
  input                                              scrmbl_mtx_gnt_i,
  // Scrambling datapath interface
  output otp_scrmbl_cmd_e                            scrmbl_cmd_o,
  output digest_mode_e                               scrmbl_mode_o,
  output logic [ConstSelWidth-1:0]                   scrmbl_sel_o,
  output logic [ScrmblBlockWidth-1:0]                scrmbl_data_o,
  output logic                                       scrmbl_valid_o,
  input  logic                                       scrmbl_ready_i,
  input  logic                                       scrmbl_valid_i,
  input  logic [ScrmblBlockWidth-1:0]                scrmbl_data_i
);

  import prim_util_pkg::vbits;

  ////////////////////////
  // Integration Checks //
  ////////////////////////

  // LC, 2xFlash, OTBN + SRAM slots
  localparam int NumReq = 4 + NumSramKeyReqSlots;
  // Make sure key sizes in the system are multiples of 64bit and not larger than 256bit.
  `ASSERT_INIT(KeyNonceSize0_A, (FlashKeySeedWidth <= 256) && ((FlashKeySeedWidth % 64) == 0))
  `ASSERT_INIT(KeyNonceSize1_A, (SramKeySeedWidth  <= 256) && ((SramKeySeedWidth  % 64) == 0))
  `ASSERT_INIT(KeyNonceSize2_A, (FlashKeyWidth     <= 256) && ((FlashKeyWidth     % 64) == 0))
  `ASSERT_INIT(KeyNonceSize3_A, (SramKeyWidth      <= 256) && ((SramKeyWidth      % 64) == 0))
  `ASSERT_INIT(KeyNonceSize4_A, (SramNonceWidth    <= 256) && ((SramNonceWidth    % 64) == 0))
  `ASSERT_INIT(KeyNonceSize5_A, (OtbnKeyWidth      <= 256) && ((OtbnKeyWidth      % 64) == 0))
  `ASSERT_INIT(KeyNonceSize6_A, (OtbnNonceWidth    <= 256) && ((OtbnNonceWidth    % 64) == 0))

  // Make sure EDN interface has compatible width.
  `ASSERT_INIT(EntropyWidthDividesDigestBlockWidth_A, (ScrmblKeyWidth % EdnDataWidth) == 0)

  ///////////////////////////////////
  // Input Mapping and Arbitration //
  ///////////////////////////////////

  // The key derivation and token hashing functions are aligned such that 2 x 128bit key
  // seeds / token blocks are processed in two subsequent steps using the digest primitive.
  // This effectively compresses these blocks down into 2 x 64bit blocks, thereby creating
  // one 128bit key or token output.
  //
  // The same FSM is shared among the different flavors of key derivation and token
  // hashing functions, and the following configuration options are available:
  //
  // 1) ingest an additional 128bit entropy block after ingesting a 128bit key seed.
  // 2) keep digest state after producing the first 64bit block instead of reverting to the IV.
  // 3) netlist constant index.
  // 4) fetch additional entropy for the nonce output.
  // 5) whether or not the key seed is valid. if not, it will be defaulted to '0.
  // 6) 256bit key seed / token input.
  //
  // The configuration options are set further below, depending on the request type.

  typedef struct packed {
    logic                             ingest_entropy; // 1)
    logic                             chained_digest; // 2)
    digest_sel_e                      digest_sel;     // 3)
    logic                             fetch_nonce;    // 4)
    logic [1:0]                       nonce_size;     // 4)
    logic                             seed_valid;     // 5)
    logic [3:0][ScrmblBlockWidth-1:0] seed;           // 6)
  } req_bundle_t;

  logic [NumReq-1:0] req, gnt;
  req_bundle_t req_bundles [NumReq];

  assign req[0] = lc_otp_token_i.req;
  assign req[1] = flash_otp_key_i.data_req;
  assign req[2] = flash_otp_key_i.addr_req;
  assign req[3] = otbn_otp_key_i.req;

  assign lc_otp_token_o.ack       = gnt[0];
  assign flash_otp_key_o.data_ack = gnt[1];
  assign flash_otp_key_o.addr_ack = gnt[2];
  assign otbn_otp_key_o.ack       = gnt[3];

  // Life cycle unlock token.
  assign req_bundles[0] = '{ingest_entropy: 1'b0, // no random entropy added
                            chained_digest: 1'b1, // do not revert to netlist IV between blocks
                            digest_sel:     LcRawDigest,
                            fetch_nonce:    1'b0, // no nonce needed
                            nonce_size:     '0,
                            seed_valid:     1'b1, // valid if request is valid
                            seed:           {lc_otp_token_i.token_input,  // reuse same seed
                                             lc_otp_token_i.token_input}};
  // Flash data key
  assign req_bundles[1] = '{ingest_entropy: 1'b0, // no random entropy added
                            chained_digest: 1'b0, // revert to netlist IV between blocks
                            digest_sel:     FlashDataKey,
                            fetch_nonce:    1'b0, // no nonce needed
                            nonce_size:     '0,
                            seed_valid:     scrmbl_key_seed_valid_i,
                            seed:           flash_data_key_seed_i}; // 2x128bit
  // Flash addr key
  assign req_bundles[2] = '{ingest_entropy: 1'b0, // no random entropy added
                            chained_digest: 1'b0, // revert to netlist IV between blocks
                            digest_sel:     FlashAddrKey,
                            fetch_nonce:    1'b0, // no nonce needed
                            nonce_size:     '0,
                            seed_valid:     scrmbl_key_seed_valid_i,
                            seed:           flash_addr_key_seed_i}; // 2x128bit
  // OTBN key
  assign req_bundles[3] = '{ingest_entropy: 1'b1, // ingest random data
                            chained_digest: 1'b0, // revert to netlist IV between blocks
                            digest_sel:     SramDataKey,
                            fetch_nonce:    1'b1, // fetch nonce
                            nonce_size:     2'(OtbnNonceWidth/64-1),
                            seed_valid:     scrmbl_key_seed_valid_i,
                            seed:           {sram_data_key_seed_i,   // reuse same seed
                                             sram_data_key_seed_i}};

  // SRAM keys
  for (genvar k = 4; k < NumReq; k++) begin : gen_req_assign
    assign req[k]                      = sram_otp_key_i[k-4].req;
    assign sram_otp_key_o[k-4].ack = gnt[k];
    assign req_bundles[k] = '{ingest_entropy: 1'b1, // ingest random data
                              chained_digest: 1'b0, // revert to netlist IV between blocks
                              digest_sel:     SramDataKey,
                              fetch_nonce:    1'b1, // fetch nonce
                              nonce_size:     2'(SramNonceWidth/64-1),
                              seed_valid:     scrmbl_key_seed_valid_i,
                              seed:           {sram_data_key_seed_i,   // reuse same seed
                                               sram_data_key_seed_i}};
  end

  // This arbitrates among incoming key derivation requests on a
  // round robin basis to prevent deadlock.
  logic req_valid, req_ready;
  req_bundle_t req_bundle;

  prim_arbiter_tree #(
    .N(NumReq),
    .DW($bits(req_bundle_t)))
  u_req_arb (
    .clk_i,
    .rst_ni,
    .req_i   ( req         ),
    .data_i  ( req_bundles ),
    .gnt_o   ( gnt         ),
    .idx_o   (             ),
    .valid_o ( req_valid   ),
    .data_o  ( req_bundle  ),
    .ready_i ( req_ready   )
  );

  //////////////////////////////
  // Temporary Regs and Muxes //
  //////////////////////////////

  logic seed_cnt_clr, seed_cnt_en, entropy_cnt_clr, entropy_cnt_en;
  logic [1:0] seed_cnt_d, seed_cnt_q, entropy_cnt_d, entropy_cnt_q;

  assign seed_cnt_d    = (seed_cnt_clr)    ? '0 :
                         (seed_cnt_en)     ? seed_cnt_q + 1'b1 : seed_cnt_q;
  assign entropy_cnt_d = (entropy_cnt_clr) ? '0 :
                         (entropy_cnt_en)  ? entropy_cnt_q + 1'b1 : entropy_cnt_q;

  logic seed_valid_reg_en;
  logic key_reg_en, nonce_reg_en;
  logic seed_valid_d, seed_valid_q;
  logic [ScrmblKeyWidth/ScrmblBlockWidth-1:0][ScrmblBlockWidth-1:0] key_out_d, key_out_q;
  logic [3:0][ScrmblBlockWidth-1:0] nonce_out_d, nonce_out_q;

  always_comb begin : p_outregs
    key_out_d    = key_out_q;
    nonce_out_d  = nonce_out_q;
    seed_valid_d = seed_valid_q;
    if (key_reg_en) begin
      key_out_d[seed_cnt_q[1]] = scrmbl_data_i;
    end
    if (nonce_reg_en) begin
      nonce_out_d[entropy_cnt_q] = edn_data_i;
    end
    if (seed_valid_reg_en) begin
      seed_valid_d = req_bundle.seed_valid;
    end
  end

  // Connect keys/nonce outputs to output regs.
  assign lc_otp_token_o.hashed_token = key_out_q;
  assign flash_otp_key_o.key         = key_out_q;
  assign flash_otp_key_o.seed_valid  = seed_valid_q;
  assign otbn_otp_key_o.key          = key_out_q;
  assign otbn_otp_key_o.nonce        = nonce_out_q;
  assign otbn_otp_key_o.seed_valid   = seed_valid_q;

  for (genvar k = 0; k < NumSramKeyReqSlots; k++) begin : gen_out_assign
    assign sram_otp_key_o[k].key        = key_out_q;
    assign sram_otp_key_o[k].nonce      = nonce_out_q[0];
    assign sram_otp_key_o[k].seed_valid = seed_valid_q;
  end

  typedef enum logic {
    SeedData,
    EntropyData
  } data_sel_e;

  // Select correct 64bit block.
  data_sel_e data_sel;
  assign scrmbl_data_o = (data_sel == EntropyData) ? nonce_out_q[entropy_cnt_q[0]] :
                        // Gate seed value to '0 if invalid.
                         (req_bundle.seed_valid)   ? req_bundle.seed[seed_cnt_q]   : '0;

  /////////////////
  // Control FSM //
  /////////////////

  // Encoding generated with:
  // $ ./sparse-fsm-encode.py -d 5 -m 11 -n 10 \
  //      -s 2544133835 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (54.55%)
  //  6: |||||||||||||||| (45.45%)
  //  7: --
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    ResetSt        = 10'b0111100000,
    IdleSt         = 10'b0001111101,
    DigClrSt       = 10'b1101101011,
    DigLoadSt      = 10'b0100011010,
    FetchEntropySt = 10'b0010001001,
    DigEntropySt   = 10'b0110110111,
    DigFinSt       = 10'b0001000110,
    DigWaitSt      = 10'b1100000101,
    FetchNonceSt   = 10'b1010101110,
    FinishSt       = 10'b1111011100,
    ErrorSt        = 10'b1011010011
  } state_e;

  state_e state_d, state_q;

  always_comb begin : p_fsm
    state_d = state_q;

    // FSM Error output
    fsm_err_o = 1'b0;

    // Counters
    seed_cnt_en     = 1'b0;
    seed_cnt_clr    = 1'b0;
    entropy_cnt_en  = 1'b0;
    entropy_cnt_clr = 1'b0;

    // EDN 128bit block fetch request
    edn_req_o = 1'b0;

    // Data selection and temp registers
    data_sel          = SeedData;
    key_reg_en        = 1'b0;
    nonce_reg_en      = 1'b0;
    seed_valid_reg_en = 1'b0;

    // Scrambling datapath
    scrmbl_mtx_req_o = 1'b0;
    scrmbl_sel_o     = req_bundle.digest_sel;
    scrmbl_cmd_o     = LoadShadow;
    scrmbl_mode_o    = StandardMode;

    scrmbl_valid_o   = 1'b0;

    // Request acknowledgement
    req_ready = 1'b0;

    unique case (state_q)
      ///////////////////////////////////////////////////////////////////
      // State right after reset. Wait here until KDI gets enabled.
      ResetSt: begin
        if (kdi_en_i) begin
          state_d = IdleSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for a request, then go and acquire the mutex.
      IdleSt: begin
        if (req_valid) begin
          state_d = DigClrSt;
          seed_cnt_clr    = 1'b1;
          entropy_cnt_clr = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // First, acquire the mutex for the digest and clear the digest state.
      DigClrSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        // Need to reset the digest state and set digest mode to "standard".
        scrmbl_cmd_o = DigestInit;
        if (scrmbl_mtx_gnt_i && scrmbl_ready_i) begin
          state_d = DigLoadSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Load two 64bit blocks of the seed, and trigger digest calculation.
      DigLoadSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        // Trigger digest round in case this is the second block in a row.
        if (seed_cnt_q[0]) begin
          scrmbl_cmd_o = Digest;
          if (scrmbl_ready_i) begin
            // Go and ingest a block of entropy if required.
            if (req_bundle.ingest_entropy) begin
              state_d = FetchEntropySt;
            // Otherwise go to digest finalization state.
            end else begin
              state_d = DigFinSt;
            end
          end
        // Just load first 64bit block and stay here.
        end else if (scrmbl_ready_i) begin
          seed_cnt_en  = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Fetch random data to ingest for key derivation.
      FetchEntropySt: begin
        scrmbl_mtx_req_o = 1'b1;
        edn_req_o = 1'b1;
        if (edn_ack_i) begin
          nonce_reg_en = 1'b1;
          // Finished, go and acknowledge this request.
          if (entropy_cnt_q == 2'h1) begin
            state_d = DigEntropySt;
            entropy_cnt_clr = 1'b1;
          // Keep on requesting entropy.
          end else begin
            entropy_cnt_en = 1'b1;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Load two 64bit blocks of entropy data.
      DigEntropySt: begin
        scrmbl_mtx_req_o = 1'b1;
        data_sel = EntropyData;
        scrmbl_valid_o = 1'b1;
        // Trigger digest round in case this is the second block in a row,
        // and go to digest finalization.
        if (entropy_cnt_q[0]) begin
          scrmbl_cmd_o = Digest;
          if (scrmbl_ready_i) begin
            state_d = DigFinSt;
            entropy_cnt_clr = 1'b1;
          end
        // Just load first 64bit block and stay here.
        end else if (scrmbl_ready_i) begin
          entropy_cnt_en = 1'b1;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Trigger digest finalization and go wait for the result.
      DigFinSt: begin
        scrmbl_mtx_req_o = 1'b1;
        scrmbl_valid_o = 1'b1;
        scrmbl_cmd_o = DigestFinalize;
        if (scrmbl_ready_i) begin
          state_d = DigWaitSt;
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Wait for the digest to return, and write the result to the key
      // output register. Go back and process the second part of the
      // input seed if needed.
      DigWaitSt: begin
        scrmbl_mtx_req_o = 1'b1;
        if (scrmbl_valid_i) begin
          key_reg_en = 1'b1;
          // Not finished yet, need to go back and produce second 64bit block.
          if (seed_cnt_q == 2'h1) begin
            seed_cnt_en  = 1'b1;
            // In this case the previous digest state is kept,
            // which leads to a chained digest.
            if (req_bundle.chained_digest) begin
              state_d = DigLoadSt;
            // In this case we revert the digest state to the netlist IV.
            end else begin
              state_d = DigClrSt;
            end
          // This was the second 64bit output block.
          end else begin
            seed_cnt_clr = 1'b1;
            // Make sure we output the status of the key seed in OTP.
            seed_valid_reg_en = 1'b1;
            // Check whether we need to fetch additional nonce data.
            if (req_bundle.fetch_nonce) begin
              state_d = FetchNonceSt;
            end else begin
              // Finished, go and acknowledge this request.
              state_d = FinishSt;
            end
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Fetch additional nonce data. Note that the mutex is released in
      // this state.
      FetchNonceSt: begin
        edn_req_o = 1'b1;
        if (edn_ack_i) begin
          nonce_reg_en = 1'b1;
          // Finished, go and acknowledge this request.
          if (entropy_cnt_q == req_bundle.nonce_size) begin
            state_d = FinishSt;
            entropy_cnt_clr = 1'b1;
          // Keep on requesting entropy.
          end else begin
            entropy_cnt_en = 1'b1;
          end
        end
      end
      ///////////////////////////////////////////////////////////////////
      // Acknowledge request and go back to IdleSt.
      FinishSt: begin
        state_d = IdleSt;
        req_ready = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
      // Terminal error state. This raises an alert.
      ErrorSt: begin
        fsm_err_o = 1'b1;
      end
      ///////////////////////////////////////////////////////////////////
      // This should never happen, hence we directly jump into the
      // error state, where an alert will be triggered.
      default: begin
        state_d = ErrorSt;
      end
      ///////////////////////////////////////////////////////////////////
    endcase // state_q

    // Unconditionally jump into the terminal error state in case of escalation.
    if (escalate_en_i != lc_ctrl_pkg::Off) begin
      state_d = ErrorSt;
    end
  end

  ///////////////
  // Registers //
  ///////////////

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(ResetSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d     ),
    .q_o ( state_raw_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      seed_cnt_q    <= '0;
      entropy_cnt_q <= '0;
      key_out_q     <= '0;
      nonce_out_q   <= '0;
      seed_valid_q  <= 1'b0;
    end else begin
      seed_cnt_q    <= seed_cnt_d;
      entropy_cnt_q <= entropy_cnt_d;
      key_out_q     <= key_out_d;
      nonce_out_q   <= nonce_out_d;
      seed_valid_q  <= seed_valid_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(FsmErrKnown_A,             fsm_err_o)
  `ASSERT_KNOWN(EdnReqKnown_A,             edn_req_o)
  `ASSERT_KNOWN(LcOtpTokenRspKnown_A,      lc_otp_token_o)
  `ASSERT_KNOWN(FlashOtpKeyRspKnown_A,     flash_otp_key_o)
  `ASSERT_KNOWN(SramOtpKeyRspKnown_A,      sram_otp_key_o)
  `ASSERT_KNOWN(OtbnOtpKeyRspKnown_A,      otbn_otp_key_o)
  `ASSERT_KNOWN(ScrmblMtxReqKnown_A,       scrmbl_mtx_req_o)
  `ASSERT_KNOWN(ScrmblCmdKnown_A,          scrmbl_cmd_o)
  `ASSERT_KNOWN(ScrmblModeKnown_A,         scrmbl_mode_o)
  `ASSERT_KNOWN(ScrmblSelKnown_A,          scrmbl_sel_o)
  `ASSERT_KNOWN(ScrmblDataKnown_A,         scrmbl_data_o)
  `ASSERT_KNOWN(ScrmblValidKnown_A,        scrmbl_valid_o)

endmodule : otp_ctrl_kdi
