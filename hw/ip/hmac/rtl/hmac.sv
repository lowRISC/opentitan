// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// HMAC-SHA256

`include "prim_assert.sv"

module hmac
  import hmac_pkg::*;
  import hmac_reg_pkg::*;
(
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  output logic intr_hmac_done_o,
  output logic intr_fifo_empty_o,
  output logic intr_hmac_err_o,

  output logic idle_o
);


  /////////////////////////
  // Signal declarations //
  /////////////////////////
  hmac_reg2hw_t reg2hw;
  hmac_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t  tl_win_h2d[1];
  tlul_pkg::tl_d2h_t  tl_win_d2h[1];

  logic [255:0] secret_key;

  logic        wipe_secret;
  logic [31:0] wipe_v;

  logic        fifo_rvalid;
  logic        fifo_rready;
  sha_fifo_t   fifo_rdata;

  logic        fifo_wvalid, fifo_wready;
  sha_fifo_t   fifo_wdata;
  logic        fifo_full;
  logic        fifo_empty;
  logic [4:0]  fifo_depth;

  logic        msg_fifo_req;
  logic        msg_fifo_gnt;
  logic        msg_fifo_we;
  logic [8:0]  msg_fifo_addr;   // NOT_READ
  logic [31:0] msg_fifo_wdata;
  logic [31:0] msg_fifo_wmask;
  logic [31:0] msg_fifo_rdata;
  logic        msg_fifo_rvalid;
  logic [1:0]  msg_fifo_rerror;
  logic [31:0] msg_fifo_wdata_endian;
  logic [31:0] msg_fifo_wmask_endian;

  logic        packer_ready;
  logic        packer_flush_done;

  logic        reg_fifo_wvalid;
  sha_word_t   reg_fifo_wdata;
  sha_word_t   reg_fifo_wmask;
  logic        hmac_fifo_wsel;
  logic        hmac_fifo_wvalid;
  logic [2:0]  hmac_fifo_wdata_sel;

  logic        shaf_rvalid;
  sha_fifo_t   shaf_rdata;
  logic        shaf_rready;

  logic        sha_en;
  logic        hmac_en;
  logic        endian_swap;
  logic        digest_swap;

  logic        reg_hash_start;
  logic        sha_hash_start;
  logic        hash_start;      // Valid hash_start_signal
  logic        reg_hash_process;
  logic        sha_hash_process;

  logic        reg_hash_done;
  logic        sha_hash_done;

  logic [63:0] message_length;
  logic [63:0] sha_message_length;

  err_code_e   err_code;
  logic        err_valid;

  sha_word_t [7:0] digest;

  hmac_reg2hw_cfg_reg_t cfg_reg;
  logic                 cfg_block;  // Prevent changing config
  logic                 msg_allowed; // MSG_FIFO from software is allowed

  ///////////////////////
  // Connect registers //
  ///////////////////////
  assign hw2reg.status.fifo_full.d  = fifo_full;
  assign hw2reg.status.fifo_empty.d = fifo_empty;
  assign hw2reg.status.fifo_depth.d = fifo_depth;

  // secret key
  assign wipe_secret = reg2hw.wipe_secret.qe;
  assign wipe_v      = reg2hw.wipe_secret.q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      secret_key <= '0;
    end else if (wipe_secret) begin
      secret_key <= secret_key ^ {8{wipe_v}};
    end else if (!cfg_block) begin
      // Allow updating secret key only when the engine is in Idle.
      for (int i = 0; i < 8; i++) begin
        if (reg2hw.key[7-i].qe) begin
          secret_key[32*i+:32] <= reg2hw.key[7-i].q;
        end
      end
    end
  end

  for (genvar i = 0; i < 8; i++) begin : gen_key_digest
    assign hw2reg.key[7-i].d      = '0;
    // digest
    assign hw2reg.digest[i].d = conv_endian(digest[i], digest_swap);
  end

  logic [3:0] unused_cfg_qe;

  assign unused_cfg_qe = {cfg_reg.sha_en.qe,      cfg_reg.hmac_en.qe,
                          cfg_reg.endian_swap.qe, cfg_reg.digest_swap.qe};

  assign sha_en      = cfg_reg.sha_en.q;
  assign hmac_en     = cfg_reg.hmac_en.q;
  assign endian_swap = cfg_reg.endian_swap.q;
  assign digest_swap = cfg_reg.digest_swap.q;
  assign hw2reg.cfg.hmac_en.d     = cfg_reg.hmac_en.q;
  assign hw2reg.cfg.sha_en.d      = cfg_reg.sha_en.q;
  assign hw2reg.cfg.endian_swap.d = cfg_reg.endian_swap.q;
  assign hw2reg.cfg.digest_swap.d = cfg_reg.digest_swap.q;

  assign reg_hash_start   = reg2hw.cmd.hash_start.qe   & reg2hw.cmd.hash_start.q;
  assign reg_hash_process = reg2hw.cmd.hash_process.qe & reg2hw.cmd.hash_process.q;

  // Error code register
  assign hw2reg.err_code.de = err_valid;
  assign hw2reg.err_code.d  = err_code;

  /////////////////////
  // Control signals //
  /////////////////////
  assign hash_start = reg_hash_start & sha_en & ~cfg_block;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cfg_block <= '0;
    end else if (hash_start) begin
      cfg_block <= 1'b 1;
    end else if (reg_hash_done) begin
      cfg_block <= 1'b 0;
    end
  end
  // Hold the configuration during the process
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cfg_reg <= '{endian_swap: '{q: 1'b1, qe: 1'b0}, default:'0};
    end else if (!cfg_block && reg2hw.cfg.hmac_en.qe) begin
      cfg_reg <= reg2hw.cfg ;
    end
  end

  // Open up the MSG_FIFO from the TL-UL port when it is ready
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      msg_allowed <= '0;
    end else if (hash_start) begin
      msg_allowed <= 1'b 1;
    end else if (packer_flush_done) begin
      msg_allowed <= 1'b 0;
    end
  end
  ////////////////
  // Interrupts //
  ////////////////
  logic fifo_empty_q, fifo_empty_event;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fifo_empty_q <= '1; // By default, it is empty
    end else if (!hmac_fifo_wsel) begin
      fifo_empty_q <= fifo_empty;
    end
  end
  assign fifo_empty_event = fifo_empty & ~fifo_empty_q;

  logic [2:0] event_intr;
  assign event_intr = {err_valid, fifo_empty_event, reg_hash_done};

  // instantiate interrupt hardware primitive
  prim_intr_hw #(.Width(1)) intr_hw_hmac_done (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_intr[0]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.hmac_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.hmac_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.hmac_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.hmac_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.hmac_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.hmac_done.d),
    .intr_o                 (intr_hmac_done_o)
  );
  prim_intr_hw #(.Width(1)) intr_hw_fifo_empty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_intr[1]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.fifo_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.fifo_empty.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.fifo_empty.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.fifo_empty.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.fifo_empty.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.fifo_empty.d),
    .intr_o                 (intr_fifo_empty_o)
  );
  prim_intr_hw #(.Width(1)) intr_hw_hmac_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_intr[2]),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.hmac_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.hmac_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.hmac_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.hmac_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.hmac_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.hmac_err.d),
    .intr_o                 (intr_hmac_err_o)
  );

  ///////////////
  // Instances //
  ///////////////

  assign msg_fifo_rvalid = msg_fifo_req & ~msg_fifo_we;
  assign msg_fifo_rdata  = '1;  // Return all F
  assign msg_fifo_rerror = '1;  // Return error for read access
  assign msg_fifo_gnt    = msg_fifo_req & ~hmac_fifo_wsel & packer_ready;

  // FIFO control
  sha_fifo_t reg_fifo_wentry;
  assign reg_fifo_wentry.data = conv_endian(reg_fifo_wdata, 1'b1); // always convert
  assign reg_fifo_wentry.mask = {reg_fifo_wmask[0],  reg_fifo_wmask[8],
                                 reg_fifo_wmask[16], reg_fifo_wmask[24]};
  assign fifo_full   = ~fifo_wready;
  assign fifo_empty  = ~fifo_rvalid;
  assign fifo_wvalid = (hmac_fifo_wsel && fifo_wready) ? hmac_fifo_wvalid : reg_fifo_wvalid;
  assign fifo_wdata  = (hmac_fifo_wsel) ? '{data: digest[hmac_fifo_wdata_sel], mask: '1}
                                       : reg_fifo_wentry;

  prim_fifo_sync #(
    .Width   ($bits(sha_fifo_t)),
    .Pass    (1'b1),
    .Depth   (MsgFifoDepth)
  ) u_msg_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),

    .wvalid_i(fifo_wvalid & sha_en),
    .wready_o(fifo_wready),
    .wdata_i (fifo_wdata),

    .depth_o (fifo_depth),

    .rvalid_o(fifo_rvalid),
    .rready_i(fifo_rready),
    .rdata_o (fifo_rdata)
  );

  // TL ADAPTER SRAM
  tlul_adapter_sram #(
    .SramAw (9),
    .SramDw (32),
    .Outstanding (1),
    .ByteAccess  (1),
    .ErrOnRead   (1)
  ) u_tlul_adapter (
    .clk_i,
    .rst_ni,
    .tl_i   (tl_win_h2d[0]),
    .tl_o   (tl_win_d2h[0]),

    .req_o    (msg_fifo_req   ),
    .gnt_i    (msg_fifo_gnt   ),
    .we_o     (msg_fifo_we    ),
    .addr_o   (msg_fifo_addr  ), // Doesn't care the address other than sub-word
    .wdata_o  (msg_fifo_wdata ),
    .wmask_o  (msg_fifo_wmask ),
    .rdata_i  (msg_fifo_rdata ),
    .rvalid_i (msg_fifo_rvalid),
    .rerror_i (msg_fifo_rerror)
  );

  // TL-UL to MSG_FIFO byte write handling
  logic msg_write;

  assign msg_write = msg_fifo_req & msg_fifo_we & ~hmac_fifo_wsel & msg_allowed;

  logic [$clog2(32+1)-1:0] wmask_ones;

  always_comb begin
    wmask_ones = '0;
    for (int i = 0 ; i < 32 ; i++) begin
      wmask_ones = wmask_ones + msg_fifo_wmask[i];
    end
  end

  // Calculate written message
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      message_length <= '0;
    end else if (hash_start) begin
      message_length <= '0;
    end else if (msg_write && sha_en && packer_ready) begin
      message_length <= message_length + 64'(wmask_ones);
    end
  end

  assign hw2reg.msg_length_upper.de = 1'b1;
  assign hw2reg.msg_length_upper.d = message_length[63:32];
  assign hw2reg.msg_length_lower.de = 1'b1;
  assign hw2reg.msg_length_lower.d = message_length[31:0];


  // Convert endian here
  //    prim_packer always packs to the right, but SHA engine assumes incoming
  //    to be big-endian, [31:24] comes first. So, the data is reverted after
  //    prim_packer before the message fifo. here to reverse if not big-endian
  //    before pushing to the packer.
  assign msg_fifo_wdata_endian = conv_endian(msg_fifo_wdata, ~endian_swap);
  assign msg_fifo_wmask_endian = conv_endian(msg_fifo_wmask, ~endian_swap);

  prim_packer #(
    .InW      (32),
    .OutW     (32)
  ) u_packer (
    .clk_i,
    .rst_ni,

    .valid_i      (msg_write & sha_en),
    .data_i       (msg_fifo_wdata_endian),
    .mask_i       (msg_fifo_wmask_endian),
    .ready_o      (packer_ready),

    .valid_o      (reg_fifo_wvalid),
    .data_o       (reg_fifo_wdata),
    .mask_o       (reg_fifo_wmask),
    .ready_i      (fifo_wready & ~hmac_fifo_wsel),

    .flush_i      (reg_hash_process),
    .flush_done_o (packer_flush_done) // ignore at this moment
  );


  hmac_core u_hmac (
    .clk_i,
    .rst_ni,

    .secret_key,

    .wipe_secret,
    .wipe_v,

    .hmac_en,

    .reg_hash_start   (hash_start),
    .reg_hash_process (packer_flush_done), // Trigger after all msg written
    .hash_done      (reg_hash_done),
    .sha_hash_start,
    .sha_hash_process,
    .sha_hash_done,

    .sha_rvalid     (shaf_rvalid),
    .sha_rdata      (shaf_rdata),
    .sha_rready     (shaf_rready),

    .fifo_rvalid,
    .fifo_rdata,
    .fifo_rready,

    .fifo_wsel      (hmac_fifo_wsel),
    .fifo_wvalid    (hmac_fifo_wvalid),
    .fifo_wdata_sel (hmac_fifo_wdata_sel),
    .fifo_wready,

    .message_length,
    .sha_message_length
  );

  sha2 u_sha2 (
    .clk_i,
    .rst_ni,

    .wipe_secret,
    .wipe_v,

    .fifo_rvalid      (shaf_rvalid),
    .fifo_rdata       (shaf_rdata),
    .fifo_rready      (shaf_rready),

    .sha_en,
    .hash_start       (sha_hash_start),
    .hash_process     (sha_hash_process),
    .hash_done        (sha_hash_done),

    .message_length   (sha_message_length),

    .digest
  );

  hmac_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .tl_win_o   (tl_win_h2d),
    .tl_win_i   (tl_win_d2h),

    .reg2hw,
    .hw2reg,

    .devmode_i  (1'b1)
  );

  /////////////////////////
  // HMAC Error Handling //
  /////////////////////////
  logic msg_push_sha_disabled, hash_start_sha_disabled, update_seckey_inprocess;
  logic hash_start_active;  // `reg_hash_start` set when hash already in active
  logic msg_push_not_allowed; // Message is received when `hash_start` isn't set
  assign msg_push_sha_disabled = msg_write & ~sha_en;
  assign hash_start_sha_disabled = reg_hash_start & ~sha_en;
  assign hash_start_active = reg_hash_start & cfg_block;
  assign msg_push_not_allowed = msg_fifo_req & ~msg_allowed;

  always_comb begin
    update_seckey_inprocess = 1'b0;
    if (cfg_block) begin
      for (int i = 0 ; i < 8 ; i++) begin
        if (reg2hw.key[i].qe) begin
          update_seckey_inprocess = update_seckey_inprocess | 1'b1;
        end
      end
    end else begin
      update_seckey_inprocess = 1'b0;
    end
  end

  // Update ERR_CODE register and interrupt only when no pending interrupt.
  // This ensures only the first event of the series of events can be seen to sw.
  // It is recommended that the software reads ERR_CODE register when interrupt
  // is pending to avoid any race conditions.
  assign err_valid = ~reg2hw.intr_state.hmac_err.q &
                   ( msg_push_sha_disabled | hash_start_sha_disabled
                   | update_seckey_inprocess | hash_start_active
                   | msg_push_not_allowed );

  always_comb begin
    err_code = NoError;
    unique case (1'b1)
      msg_push_sha_disabled: begin
        err_code = SwPushMsgWhenShaDisabled;
      end
      hash_start_sha_disabled: begin
        err_code = SwHashStartWhenShaDisabled;
      end

      update_seckey_inprocess: begin
        err_code = SwUpdateSecretKeyInProcess;
      end

      hash_start_active: begin
        err_code = SwHashStartWhenActive;
      end

      msg_push_not_allowed: begin
        err_code = SwPushMsgWhenDisallowed;
      end

      default: begin
        err_code = NoError;
      end
    endcase
  end

  /////////////////////
  // Idle output     //
  /////////////////////
  // TBD this should be connected later
  assign idle_o = 1'b1;

  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  //////////////////////////////////////////////

`ifndef VERILATOR
`ifndef SYNTHESIS
  // HMAC assumes TL-UL mask is byte-aligned.
  property wmask_bytealign_p(wmask_byte, clk, rst_n);
    @(posedge clk) disable iff (rst_n == 0)
      msg_fifo_req & msg_fifo_we |-> wmask_byte inside {'0, '1};
  endproperty

  for (genvar i = 0 ; i < 4; i++) begin: gen_assert_wmask_bytealign
    assert property (wmask_bytealign_p(msg_fifo_wmask[8*i+:8], clk_i, rst_ni));
  end

  // To pass FPV, this shouldn't add pragma translate_off even these two signals
  // are used in Assertion only
  logic in_process;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)               in_process <= 1'b0;
    else if (reg_hash_process) in_process <= 1'b1;
    else if (reg_hash_done)    in_process <= 1'b0;
  end

  logic initiated;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)               initiated <= 1'b0;
    else if (hash_start)       initiated <= 1'b1;
    else if (reg_hash_process) initiated <= 1'b0;
  end

  // the host doesn't write data after hash_process until hash_start.
  // Same as "message_length shouldn't be changed between hash_process and done
  `ASSERT(ValidWriteAssert, msg_fifo_req |-> !in_process)

  // `hash_process` shall be toggle and paired with `hash_start`.
  // Below condition is covered by the design (2020-02-19)
  //`ASSERT(ValidHashStartAssert, hash_start |-> !initiated)
  `ASSERT(ValidHashProcessAssert, reg_hash_process |-> initiated)

  // between `hash_done` and `hash_start`, message FIFO should be empty
  `ASSERT(MsgFifoEmptyWhenNoOpAssert,
          !in_process && !initiated |-> $stable(message_length))

  // hmac_en should be modified only when the logic is Idle
  `ASSERT(ValidHmacEnConditionAssert,
          hmac_en != $past(hmac_en) |-> !in_process && !initiated)

  // All outputs should be known value after reset
  `ASSERT_KNOWN(IntrHmacDoneOKnown, intr_hmac_done_o)
  `ASSERT_KNOWN(IntrFifoEmptyOKnown, intr_fifo_empty_o)
  `ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown, tl_o.a_ready)

`endif // SYNTHESIS
`endif // VERILATOR

endmodule
