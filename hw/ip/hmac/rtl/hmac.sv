// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// HMAC/SHA-2 256/384/512

`include "prim_assert.sv"

module hmac
  import prim_sha2_pkg::*;
  import hmac_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  output logic intr_hmac_done_o,
  output logic intr_fifo_empty_o,
  output logic intr_hmac_err_o,

  output prim_mubi_pkg::mubi4_t idle_o
);


  /////////////////////////
  // Signal declarations //
  /////////////////////////
  hmac_reg2hw_t reg2hw;
  hmac_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t  tl_win_h2d;
  tlul_pkg::tl_d2h_t  tl_win_d2h;

  logic [1023:0] secret_key, secret_key_d;

  // Logic will support key length <= block size
  // Will default to key length = block size, if key length > block size or unsupported value
  key_length_e key_length_supplied, key_length;

  logic        wipe_secret;
  logic [31:0] wipe_v;

  logic        fifo_rvalid;
  logic        fifo_rready;
  sha_fifo32_t fifo_rdata;

  logic        fifo_wvalid, fifo_wready;
  sha_fifo32_t fifo_wdata;
  logic        fifo_full;
  logic        fifo_empty;
  logic [5:0]  fifo_depth;

  logic        msg_fifo_req;
  logic        msg_fifo_gnt;
  logic        msg_fifo_we;
  logic [31:0] msg_fifo_wdata;
  logic [31:0] msg_fifo_wmask;
  logic [31:0] msg_fifo_rdata;
  logic        msg_fifo_rvalid;
  logic [1:0]  msg_fifo_rerror;
  logic [31:0] msg_fifo_wdata_endian;
  logic [31:0] msg_fifo_wmask_endian;

  logic        packer_ready;
  logic        packer_flush_done;

  logic         reg_fifo_wvalid;
  sha_word32_t  reg_fifo_wdata;
  sha_word32_t  reg_fifo_wmask;
  logic         hmac_fifo_wsel;
  logic         hmac_fifo_wvalid;
  logic [3:0]   hmac_fifo_wdata_sel;

  logic         shaf_rvalid;
  sha_fifo32_t  shaf_rdata;
  logic         shaf_rready;

  logic        sha_en;
  logic        hmac_en;
  logic        endian_swap;
  logic        digest_swap;

  logic        reg_hash_start;
  logic        sha_hash_start;
  logic        reg_hash_stop;
  logic        reg_hash_continue;
  logic        sha_hash_continue;
  logic        hash_start;     // hash_start is reg_hash_start gated with extra checks
  logic        hash_continue;  // hash_continue is reg_hash_continue gated with extra checks
  logic        hash_process;   // hash_process is reg_hash_process gated with extra checks
  logic        hash_start_or_continue;
  logic        hash_done_event;
  logic        reg_hash_process;
  logic        sha_hash_process;

  logic        reg_hash_done;
  logic        sha_hash_done;

  logic [63:0] message_length, message_length_d;
  logic [63:0] sha_message_length;

  err_code_e  err_code;
  logic       err_valid;
  logic       invalid_config; // HMAC/SHA-2 is configured with invalid digest size/key length
  logic       invalid_config_atstart;

  sha_word64_t [7:0] digest, digest_sw;
  logic [7:0]        digest_sw_we;
  sha_word64_t       inter_digest;

  digest_mode_e digest_size, digest_size_supplied;
  // this is the digest size captured into HMAC when it gets started
  digest_mode_e digest_size_started_d, digest_size_started_q;

  hmac_reg2hw_cfg_reg_t cfg_reg;
  logic                 cfg_block;   // Prevents changing config
  logic                 msg_allowed; // MSG_FIFO from software is allowed

  logic hmac_core_idle;
  logic sha_core_idle;
  logic hash_running;
  logic idle;

  ///////////////////////
  // Connect registers //
  ///////////////////////
  assign hw2reg.status.fifo_full.d  = fifo_full;
  assign hw2reg.status.fifo_empty.d = fifo_empty;
  assign hw2reg.status.fifo_depth.d = fifo_depth;

  typedef enum logic [1:0] {
    DoneAwaitCmd,
    DoneAwaitHashDone,
    DoneAwaitMessageComplete,
    DoneAwaitHashComplete
  } done_state_e;

  done_state_e done_state_d, done_state_q;

  always_comb begin
    done_state_d = done_state_q;
    hash_done_event = 1'b0;

    unique case (done_state_q)
      DoneAwaitCmd: begin
        if (sha_hash_process) begin
          // SHA has been told to process the message, so signal *done* when the hash is done.
          done_state_d = DoneAwaitHashDone;
        end else if (reg_hash_stop) begin
          // SHA has been told to stop, so first wait for the current message block to be complete.
          done_state_d = DoneAwaitMessageComplete;
        end
      end

      DoneAwaitHashDone: begin
        if (reg_hash_done) begin
          hash_done_event = 1'b1;
          done_state_d = DoneAwaitCmd;
        end
      end

      DoneAwaitMessageComplete: begin
        if (sha_message_length[8:0] == '0 /* <=> sha_message_length % 512 == 0 */) begin
          // Once the current message block is complete, wait for the hash to complete.
          // TODO (issue #21710): handle incomplete message size and check against 512 or 1024
          done_state_d = DoneAwaitHashComplete;
        end
      end

      DoneAwaitHashComplete: begin
        if (!hash_running) begin
          hash_done_event = 1'b1;
          done_state_d = DoneAwaitCmd;
        end
      end

      default: ;
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      done_state_q <= DoneAwaitCmd;
    end else begin
      done_state_q <= done_state_d;
    end
  end

  assign wipe_secret = reg2hw.wipe_secret.qe;
  assign wipe_v      = reg2hw.wipe_secret.q;

  // update secret key
  always_comb begin : update_secret_key
    secret_key_d = secret_key;
    if (wipe_secret) begin
      secret_key_d = {32{wipe_v}};
    end else if (!cfg_block) begin
      // Allow updating secret key only when the engine is in Idle.
      for (int i = 0; i < 32; i++) begin
        if (reg2hw.key[31-i].qe) begin
          secret_key_d[32*i+:32] = reg2hw.key[31-i].q;
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) secret_key <= '0;
    else         secret_key <= secret_key_d;
  end

  for (genvar i = 0; i < 32; i++) begin : gen_key
    assign hw2reg.key[31-i].d      = '0;
  end

  // Retain the previous digest in CSRs until HMAC is actually started with a valid configuration
  always_comb begin : assign_digest_reg
    for (int i = 0; i < 16; i++) begin
      // default
      if (i < 8) begin
        // digest SW -> HW
        digest_sw[i]    = '0;
        digest_sw_we[i] = '0;
      end
      // digest HW -> SW
      hw2reg.digest[i].d = '0;

      if (digest_size_started_q == SHA2_256) begin
        if (i < 8) begin
          // digest HW -> SW
          hw2reg.digest[i].d = conv_endian32(digest[i][31:0], digest_swap);
          // digest SW -> HW
          digest_sw[i]       = {32'h0, conv_endian32(reg2hw.digest[i].q, digest_swap)};
          digest_sw_we[i]    = reg2hw.digest[i].qe;
        end else begin
          hw2reg.digest[i].d = '0;
        end
      end else if ((digest_size_started_q == SHA2_384) || (digest_size_started_q == SHA2_512)) begin
        if (i % 2 == 0 && i < 15) begin // even index
          // digest HW -> SW
          inter_digest       = conv_endian64(digest[i/2], digest_swap);
          hw2reg.digest[i].d = inter_digest[31:0];
          // digest SW -> HW
          digest_sw[i/2]    = conv_endian64({reg2hw.digest[i+1].q,reg2hw.digest[i].q}, digest_swap);
          digest_sw_we[i/2] = reg2hw.digest[i].qe | reg2hw.digest[i+1].qe;
        end else begin  // odd index
          inter_digest       = conv_endian64(digest[i/2], digest_swap);
          hw2reg.digest[i].d = inter_digest[63:32];
          // digest SW -> HW
          digest_sw[i/2]    = conv_endian64({reg2hw.digest[i].q,reg2hw.digest[i-1].q}, digest_swap);
          digest_sw_we[i/2] = reg2hw.digest[i].qe | reg2hw.digest[i-1].qe;
        end
      end
    end
  end

  logic unused_cfg_qe;
  assign unused_cfg_qe = ^{cfg_reg.sha_en.qe,      cfg_reg.hmac_en.qe,
                           cfg_reg.endian_swap.qe, cfg_reg.digest_swap.qe,
                           cfg_reg.digest_size.qe, cfg_reg.key_length.qe };

  assign sha_en               = cfg_reg.sha_en.q;
  assign hmac_en              = cfg_reg.hmac_en.q;

  assign digest_size_supplied = digest_mode_e'(cfg_reg.digest_size.q);
  always_comb begin : cast_digest_size
    unique case (digest_size_supplied)
      SHA2_256:  digest_size = SHA2_256;
      SHA2_384:  digest_size = SHA2_384;
      SHA2_512:  digest_size = SHA2_512;
      // unsupported digest size values are mapped to SHA2_None
      // if HMAC/SHA-2 is triggered to start with this digest size, it is blocked
      // and an error is signalled to SW
      default:   digest_size = SHA2_None;
    endcase
  end

  // Hold the previous digest size till HMAC is started with the new digest size configured
  assign digest_size_started_d = (hash_start_or_continue) ? digest_size : digest_size_started_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) digest_size_started_q <= SHA2_None;
    else         digest_size_started_q <= digest_size_started_d;
  end

  assign key_length_supplied  = key_length_e'(cfg_reg.key_length.q);
  always_comb begin : cast_key_length
    unique case (key_length_supplied)
      Key_128:  key_length = Key_128;
      Key_256:  key_length = Key_256;
      Key_384:  key_length = Key_384;
      Key_512:  key_length = Key_512;
      Key_1024: key_length = Key_1024;
      // unsupported key length values are mapped to Key_None
      // if HMAC (not SHA-2) is triggered to start with this key length, it is blocked
      // and an error is signalled to SW
      default:  key_length = Key_None;
    endcase
  end

  assign endian_swap = cfg_reg.endian_swap.q;
  assign digest_swap = cfg_reg.digest_swap.q;

  assign hw2reg.cfg.hmac_en.d     = cfg_reg.hmac_en.q;
  assign hw2reg.cfg.sha_en.d      = cfg_reg.sha_en.q;
  assign hw2reg.cfg.digest_size.d = digest_mode_e'(digest_size);
  assign hw2reg.cfg.key_length.d  = key_length_e'(key_length);
  assign hw2reg.cfg.endian_swap.d = cfg_reg.endian_swap.q;
  assign hw2reg.cfg.digest_swap.d = cfg_reg.digest_swap.q;

  assign reg_hash_start    = reg2hw.cmd.hash_start.qe & reg2hw.cmd.hash_start.q;
  assign reg_hash_stop     = reg2hw.cmd.hash_stop.qe & reg2hw.cmd.hash_stop.q;
  assign reg_hash_continue = reg2hw.cmd.hash_continue.qe & reg2hw.cmd.hash_continue.q;
  assign reg_hash_process  = reg2hw.cmd.hash_process.qe & reg2hw.cmd.hash_process.q;

  // Error code register
  assign hw2reg.err_code.de = err_valid;
  assign hw2reg.err_code.d  = err_code;

  /////////////////////
  // Control signals //
  /////////////////////
  assign hash_start             = reg_hash_start    & sha_en & ~cfg_block & ~invalid_config;
  assign hash_continue          = reg_hash_continue & sha_en & ~cfg_block & ~invalid_config;
  assign hash_process           = reg_hash_process  & sha_en & cfg_block &  ~invalid_config;
  assign hash_start_or_continue = hash_start | hash_continue;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cfg_block <= '0;
    end else if (hash_start_or_continue) begin
      cfg_block <= 1'b 1;
    end else if (reg_hash_done || reg_hash_stop) begin
      cfg_block <= 1'b 0;
    end
  end
  // Hold the configuration during the process
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cfg_reg <= '{
        hmac_en: '{
          q: 1'b0,
          qe: 1'b0
        },
        sha_en: '{
          q: 1'b0,
          qe: 1'b0
        },
        endian_swap: '{
          q: HMAC_CFG_ENDIAN_SWAP_RESVAL,
          qe: 1'b0
        },
        digest_swap: '{
          q: HMAC_CFG_DIGEST_SWAP_RESVAL,
          qe: 1'b0
        },
        digest_size: '{
          q: HMAC_CFG_DIGEST_SIZE_RESVAL,
          qe: 1'b0
        },
        key_length: '{
          q: HMAC_CFG_KEY_LENGTH_RESVAL,
          qe: 1'b0
        },
        default:'0
      };
    end else if (!cfg_block && reg2hw.cfg.hmac_en.qe) begin
      cfg_reg <= reg2hw.cfg ;
    end
  end

  // Open up the MSG_FIFO from the TL-UL port when it is ready
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      msg_allowed <= '0;
    end else if (hash_start_or_continue) begin
      msg_allowed <= 1'b 1;
    end else if (packer_flush_done) begin
      msg_allowed <= 1'b 0;
    end
  end

  ////////////////
  // Interrupts //
  ////////////////

  // instantiate interrupt hardware primitive
  prim_intr_hw #(.Width(1)) intr_hw_hmac_done (
    .clk_i,
    .rst_ni,
    .event_intr_i           (hash_done_event),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.hmac_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.hmac_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.hmac_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.hmac_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.hmac_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.hmac_done.d),
    .intr_o                 (intr_hmac_done_o)
  );

  // FIFO empty interrupt
  //
  // The FIFO empty interrupt is **not useful** for software if:
  // - The HMAC block is running in HMAC mode and performing the second round of computing the
  //   final hash of the outer key as well as the result of the first round using the inner key.
  //   The FIFO is then managed entirely by the hardware.
  // - The FIFO is currently not writeable by software.
  // - Software has already written the Process command. The HMAC block will now empty the
  //   FIFO and load its content into the SHA2 core, add the padding and then perfom
  //   the final hashing operation. Software cannot append the message further.
  // - Software has written the Stop command. The HMAC block will not wait for further input from
  //   software after finishing the current block.
  //
  // The FIFO empty interrupt can be **useful** for software in particular if:
  // - The FIFO was completely full previously. However, unless the HMAC block is currently
  //   processing a block, it always empties the message FIFO faster than software can fill it up,
  //   meaning the message FIFO is empty most of the time. Note, the empty status is signaled only
  //   once after the FIFO was completely full. The FIFO needs to be full again for the empty
  //   status to be signaled again next time it's empty.
  logic status_fifo_empty, fifo_empty_gate;
  logic fifo_empty_negedge, fifo_empty_q;
  logic fifo_full_seen_d, fifo_full_seen_q;
  assign fifo_empty_negedge = fifo_empty_q & ~fifo_empty;

  // Track whether the FIFO was full after being empty. We clear the tracking:
  // - When receiving the Start, Continue, Process or Stop command. This is to start over for the
  //   next message.
  // - When seeing a negative edge on the empty signal. This signals that software has reacted to
  //   the interrupt and is filling up the FIFO again.
  assign fifo_full_seen_d =
      fifo_full                             ? 1'b 1 :
      fifo_empty_negedge                    ? 1'b 0 :
      reg_hash_start || reg_hash_continue ||
          reg_hash_process || reg_hash_stop ? 1'b 0 : fifo_full_seen_q;

  // The interrupt is gated unless software is actually allowed to write the FIFO and the FIFO was
  // full before.
  assign fifo_empty_gate = ~msg_allowed || ~fifo_full_seen_q;

  assign status_fifo_empty = fifo_empty_gate ? 1'b 0 : fifo_empty;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fifo_empty_q     <= 1'b 0;
      fifo_full_seen_q <= 1'b 0;
    end else begin
      fifo_empty_q     <= fifo_empty;
      fifo_full_seen_q <= fifo_full_seen_d;
    end
  end

  prim_intr_hw #(
    .Width(1),
    .IntrT("Status")
  ) intr_hw_fifo_empty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (status_fifo_empty),
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
    .event_intr_i           (err_valid),
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

  /////////////////////
  // Unused Signals //
  /////////////////////
  logic unused_signals;
  assign unused_signals = ^{reg_fifo_wmask[7:1],   reg_fifo_wmask[15:9],
                            reg_fifo_wmask[23:17], reg_fifo_wmask[31:25]};

  // FIFO control: from packer into message FIFO
  sha_fifo32_t reg_fifo_wentry;
  assign reg_fifo_wentry.data = conv_endian32(reg_fifo_wdata, 1'b1); // always convert
  assign reg_fifo_wentry.mask = {reg_fifo_wmask[0],  reg_fifo_wmask[8],
                                 reg_fifo_wmask[16], reg_fifo_wmask[24]};
  assign fifo_full   = ~fifo_wready;
  assign fifo_empty  = ~fifo_rvalid;
  assign fifo_wvalid = (hmac_fifo_wsel && fifo_wready) ? hmac_fifo_wvalid : reg_fifo_wvalid;

  logic index;
  always_comb begin : select_fifo_wdata
    if (hmac_fifo_wsel) begin
      fifo_wdata = '0;
      if (digest_size == SHA2_256) begin
        // only reads out lower 32 bits of each digest word and discards upper 32-bit zero padding
        fifo_wdata = '{data: digest[hmac_fifo_wdata_sel[2:0]][31:0], mask: '1};
      end else if ((digest_size == SHA2_384) || (digest_size == SHA2_512)) begin
        // reads out first upper 32 bits then lower 32 bits of each digest word
        index = !hmac_fifo_wdata_sel[0];
        fifo_wdata = '{data: digest[hmac_fifo_wdata_sel >> 1][32*index+:32], mask: '1};
      end
    end else begin
      fifo_wdata = reg_fifo_wentry;
    end
  end

  // Extended for 1024-bit block
  localparam int MsgFifoDepth = 32;
  prim_fifo_sync #(
    .Width   ($bits(sha_fifo32_t)),
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
    .full_o  (),

    .rvalid_o(fifo_rvalid),
    .rready_i(fifo_rready),
    .rdata_o (fifo_rdata),
    .err_o   ()
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
    .tl_i             (tl_win_h2d),
    .tl_o             (tl_win_d2h),
    .en_ifetch_i      (prim_mubi_pkg::MuBi4False),
    .req_o            (msg_fifo_req   ),
    .req_type_o       (               ),
    .gnt_i            (msg_fifo_gnt   ),
    .we_o             (msg_fifo_we    ),
    .addr_o           (               ), // Doesn't care the address other than sub-word
    .wdata_o          (msg_fifo_wdata ),
    .wmask_o          (msg_fifo_wmask ),
    .intg_error_o     (               ),
    .rdata_i          (msg_fifo_rdata ),
    .rvalid_i         (msg_fifo_rvalid),
    .rerror_i         (msg_fifo_rerror),
    .rmw_in_progress_o()
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
    if (!rst_ni) message_length <= '0;
    else         message_length <= message_length_d;
  end

  always_comb begin
    message_length_d = message_length;
    if (!cfg_block) begin
      if (reg2hw.msg_length_lower.qe) begin
        message_length_d[31:0]  = reg2hw.msg_length_lower.q;
      end
      if (reg2hw.msg_length_upper.qe) begin
        message_length_d[63:32] = reg2hw.msg_length_upper.q;
      end
    end

    if (hash_start) begin
      message_length_d = '0;
    end else if (msg_write && sha_en && packer_ready) begin
      message_length_d = message_length + 64'(wmask_ones);
    end
  end

  assign hw2reg.msg_length_upper.d = message_length[63:32];
  assign hw2reg.msg_length_lower.d = message_length[31:0];

  // Convert endian here
  //    prim_packer always packs to the right, but SHA engine assumes incoming
  //    to be big-endian, [31:24] comes first. So, the data is reverted after
  //    prim_packer before the message fifo. here to reverse if not big-endian
  //    before pushing to the packer.
  assign msg_fifo_wdata_endian = conv_endian32(msg_fifo_wdata, endian_swap);
  assign msg_fifo_wmask_endian = conv_endian32(msg_fifo_wmask, endian_swap);

  prim_packer #(
    .InW          (32),
    .OutW         (32),
    .EnProtection (1'b 0)
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

    .flush_i      (hash_process),
    .flush_done_o (packer_flush_done), // ignore at this moment

    .err_o  () // Not used
  );


  hmac_core u_hmac (
    .clk_i,
    .rst_ni,
    .secret_key_i  (secret_key),
    .hmac_en_i     (hmac_en),
    .digest_size_i (digest_size),
    .key_length_i  (key_length),

    .reg_hash_start_i    (hash_start),
    .reg_hash_continue_i (hash_continue),
    .reg_hash_process_i  (packer_flush_done), // Trigger after all msg written
    .hash_done_o         (reg_hash_done),
    .sha_hash_start_o    (sha_hash_start),
    .sha_hash_continue_o (sha_hash_continue),
    .sha_hash_process_o  (sha_hash_process),
    .sha_hash_done_i     (sha_hash_done),

    .sha_rvalid_o     (shaf_rvalid),
    .sha_rdata_o      (shaf_rdata),
    .sha_rready_i     (shaf_rready),

    .fifo_rvalid_i (fifo_rvalid),
    .fifo_rdata_i  (fifo_rdata),
    .fifo_rready_o (fifo_rready),

    .fifo_wsel_o      (hmac_fifo_wsel),
    .fifo_wvalid_o    (hmac_fifo_wvalid),
    .fifo_wdata_sel_o (hmac_fifo_wdata_sel),
    .fifo_wready_i    (fifo_wready),

    .message_length_i     (message_length),
    .sha_message_length_o (sha_message_length),

    .idle_o           (hmac_core_idle)
  );

  // Instantiate SHA-2 256/384/512 engine
  prim_sha2_32 #(
      .MultimodeEn(1)
  ) u_prim_sha2_512 (
    .clk_i,
    .rst_ni,
    .wipe_secret_i        (wipe_secret),
    .wipe_v_i             (wipe_v),
    .fifo_rvalid_i        (shaf_rvalid),
    .fifo_rdata_i         (shaf_rdata),
    .fifo_rready_o        (shaf_rready),
    .sha_en_i             (sha_en),
    .hash_start_i         (sha_hash_start),
    .hash_continue_i      (sha_hash_continue),
    .digest_mode_i        (digest_size),
    .hash_process_i       (sha_hash_process),
    .message_length_i     (sha_message_length),
    .digest_i             (digest_sw),
    .digest_we_i          (digest_sw_we),
    .digest_o             (digest),
    .hash_running_o       (hash_running),
    .hash_done_o          (sha_hash_done),
    .idle_o               (sha_core_idle)
  );

  // Register top
  logic [NumAlerts-1:0] alert_test, alerts;
  hmac_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .tl_win_o   (tl_win_h2d),
    .tl_win_i   (tl_win_d2h),

    .reg2hw,
    .hw2reg,

    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (alerts[0])
  );

  // Alerts
  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  localparam logic [NumAlerts-1:0] AlertIsFatal = {1'b1};
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(AlertIsFatal[i])
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  /////////////////////////
  // HMAC Error Handling //
  /////////////////////////
  logic hash_start_sha_disabled, update_seckey_inprocess;
  logic hash_start_active;  // `reg_hash_start` or `reg_hash_continue` set when hash already active
  logic msg_push_not_allowed; // Message is received when `hash_start_or_continue` isn't set

  assign hash_start_sha_disabled = (reg_hash_start | reg_hash_continue) & ~sha_en;
  assign hash_start_active = (reg_hash_start | reg_hash_continue) & cfg_block;
  assign msg_push_not_allowed = msg_fifo_req & ~msg_allowed;

  // Invalid/unconfigured HMAC/SHA-2: not configured/invalid digest size or
  // not configured/invalid key length for HMAC mode or
  // key_length = 1024-bit for digest_size = SHA2_256 (max 512-bit is supported for SHA-2 256)
  assign invalid_config = ((digest_size == SHA2_None)            |
                           ((key_length == Key_None) && hmac_en) |
                           ((key_length == Key_1024) && (digest_size == SHA2_256) && hmac_en));

  // invalid_config at reg_hash_start will signal an error to the SW
  assign invalid_config_atstart = reg_hash_start & invalid_config;

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
                   ( hash_start_sha_disabled | update_seckey_inprocess
                   | hash_start_active | msg_push_not_allowed | invalid_config_atstart);

  always_comb begin
    err_code = NoError;
    unique case (1'b1)
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

      invalid_config_atstart: begin
        err_code = SwInvalidConfig;
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
  // Idle: AND condition of:
  //  - packer empty: Currently no way to guarantee the packer is empty.
  //    temporary, the logic uses packer output (reg_fifo_wvalid)
  //  - MSG_FIFO  --> fifo_rvalid
  //  - HMAC_CORE --> hmac_core_idle
  //  - SHA2_CORE --> sha_core_idle
  //  - Clean interrupt status
  // ICEBOX(#12958): Revise prim_packer and replace `reg_fifo_wvalid` to the
  // empty status.
  assign idle = !reg_fifo_wvalid && !fifo_rvalid
              && hmac_core_idle && sha_core_idle;

  prim_mubi_pkg::mubi4_t idle_q, idle_d;
  assign idle_d = prim_mubi_pkg::mubi4_bool_to_mubi(idle);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      idle_q <= prim_mubi_pkg::MuBi4False;
    end else begin
      idle_q <= idle_d;
    end
  end
  assign idle_o = idle_q;

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
    else if (hash_process)     in_process <= 1'b1;
    else if (reg_hash_done)    in_process <= 1'b0;
  end

  logic initiated;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                     initiated <= 1'b0;
    else if (hash_start_or_continue) initiated <= 1'b1;
    else if (hash_process)           initiated <= 1'b0;
  end

  // the host doesn't write data after hash_process until hash_start_or_continue.
  `ASSERT(ValidWriteAssert, msg_fifo_req |-> !in_process)

  // `hash_process` shall be toggled and paired with `hash_start_or_continue`.
  // Below condition is covered by the design (2020-02-19)
  //`ASSERT(ValidHashStartAssert, hash_start_or_continue |-> !initiated)
  `ASSERT(ValidHashProcessAssert, hash_process |-> initiated)

  // hmac_en should be modified only when the logic is Idle
  `ASSERT(ValidHmacEnConditionAssert,
          hmac_en != $past(hmac_en) |-> !in_process && !initiated)

  // All outputs should be known value after reset
  `ASSERT_KNOWN(IntrHmacDoneOKnown, intr_hmac_done_o)
  `ASSERT_KNOWN(IntrFifoEmptyOKnown, intr_fifo_empty_o)
  `ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown, tl_o.a_ready)
  `ASSERT_KNOWN(AlertKnownO_A, alert_tx_o)

`endif // SYNTHESIS
`endif // VERILATOR

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
