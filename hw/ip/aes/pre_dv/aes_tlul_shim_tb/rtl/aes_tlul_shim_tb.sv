// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module aes_tlul_shim_tb
  import tlul_pkg::*;
  import aes_pkg::*;
  import aes_reg_pkg::*;
  import aes_tlul_shim_tb_pkg::*;

#(
  localparam bit          AES192Enable           = 1,
  localparam bit          AESGCMEnable           = 1,
  localparam bit          SecMasking             = 1,
  localparam sbox_impl_e  SecSBoxImpl            = SBoxImplDom,
  localparam int unsigned SecStartTriggerDelay   = 0,
  localparam bit          SecAllowForcingMasks   = 0,
  localparam bit          SecSkipPRNGReseeding   = 0,
  localparam bit          EnableDataIntgGen      = 1,
  localparam bit          EnableRspDataIntgCheck = 1,
  localparam bit          DelayerEnable          = 0
 ) (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  tlul_pkg::tl_h2d_t tl_h2d;
  tlul_pkg::tl_d2h_t tl_d2h;

  tlul_pkg::tl_h2d_t tl_h2d_delayed;
  tlul_pkg::tl_d2h_t tl_d2h_delayed;

  // Use a counter to provide some entropy for visual inspection.
  logic [31:0] entropy_q;
  logic edn_req;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_entropy
    if (!rst_ni) begin
      entropy_q <= 32'h12345678;
    end else if (edn_req) begin
      entropy_q <= entropy_q + 32'h1;
    end
  end

  logic          shim_done;
  logic          shim_pop;
  shim_request_t shim_req;

  logic                      shim_hld;
  logic                      shim_error;
  logic [top_pkg::TL_DW-1:0] shim_rdata;

  logic error;
  assign error = shim_error | dpi_error;

  logic test_passed_q;
  logic test_done_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      test_passed_q <= 1'b1;
      test_done_q   <= 1'b0;
    end else if (shim_done || error) begin
      test_passed_q <= ~error;
      test_done_q   <= 1'b1;
    end
  end
  assign test_done_o = test_done_q;
  assign test_passed_o = test_passed_q;

  // The AES block is run in automatic mode, which means the status register has to be polled in
  // order to check whether an operation has finished. A convenient side-effect of this is that it
  // will generate a large number of TLUL requests, which in combination with the delayer serves as
  // a good stress test of the shim.
  logic poll;

  // Reads of the AES status registers are repeated (without popping a new request from the stack)
  // until it matches the `shim_req.mask`. Such a stall can occur when the `IDLE` bit needs to be
  // asserted before the computation can advance.
  assign poll = ~shim_hld
      & (shim_req.addr == 32'(AES_STATUS_OFFSET))
      & ~|(shim_rdata & shim_req.mask);
  assign shim_pop = ~shim_hld & ~poll;

  aes_tlul_shim_tb_reqs u_aes_tlul_shim_tb_reqs (
    .clk_i     ( clk_i     ),
    .rst_ni    ( rst_ni    ),
    .pop_req_i ( shim_pop  ),
    .req_o     ( shim_req  ),
    .done_o    ( shim_done )
  );

  tlul_adapter_shim #(
    .EnableDataIntgGen      ( EnableDataIntgGen      ),
    .EnableRspDataIntgCheck ( EnableRspDataIntgCheck )
  ) u_tlul_adapter_shim (
    .clk_i   ( clk_i          ),
    .rst_ni  ( rst_ni         ),
    .tl_i    ( tl_d2h_delayed ),
    .tl_o    ( tl_h2d         ),
    .dv_i    ( shim_req.dv    ),
    .addr_i  ( shim_req.addr  ),
    .write_i ( shim_req.write ),
    .wdata_i ( shim_req.wdata ),
    .wstrb_i ( shim_req.wstrb ),
    .size_i  ( shim_req.size  ),
    .hld_o   ( shim_hld       ),
    .rdata_o ( shim_rdata     ),
    .error_o ( shim_error     ),
    .last_i  ( shim_req.last  ),
    .user_i  ( shim_req.user  ),
    .id_i    ( shim_req.id    )
  );

  aes_tlul_shim_delayer #(
    .DelayerEnable ( DelayerEnable )
  ) u_aes_tlul_shim_delayer (
    .clk_i            ( clk_i          ),
    .rst_ni           ( rst_ni         ),
    .tl_h2d_i         ( tl_h2d         ),
    .tl_d2h_i         ( tl_d2h         ),
    .tl_h2d_delayed_o ( tl_h2d_delayed ),
    .tl_d2h_delayed_o ( tl_d2h_delayed )
  );

  aes #(
    .AES192Enable         ( AES192Enable         ),
    .AESGCMEnable         ( AESGCMEnable         ),
    .SecMasking           ( SecMasking           ),
    .SecSBoxImpl          ( SecSBoxImpl          ),
    .SecStartTriggerDelay ( SecStartTriggerDelay ),
    .SecAllowForcingMasks ( SecAllowForcingMasks ),
    .SecSkipPRNGReseeding ( SecSkipPRNGReseeding )
  ) u_aes (
    .clk_i            ( clk_i                      ),
    .rst_ni           ( rst_ni                     ),
    .rst_shadowed_ni  ( rst_ni                     ),
    .idle_o           (                            ),
    .lc_escalate_en_i ( lc_ctrl_pkg::Off           ),
    .clk_edn_i        ( clk_i                      ),
    .rst_edn_ni       ( rst_ni                     ),
    .edn_o            ( edn_req                    ),
    .edn_i            ( {edn_req, 1'b1, entropy_q} ),
    .keymgr_key_i     (                            ),
    .tl_i             ( tl_h2d_delayed             ),
    .tl_o             ( tl_d2h                     ),
    .alert_rx_i       ( alert_rx                   ),
    .alert_tx_o       ( alert_tx                   )
  );

  //////////////////////////////////////
  // AES-GCM Correctness Verification //
  //////////////////////////////////////

  // This is a sanity check verifying whether the AES-128-GCM block has correctly
  // computed the authentication tag for a single-block message
  // with a zero key and IV inputs, which is congruent to test case #2 in
  //
  // https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
  //
  // Instead of hardcoding the model tag, this testbench calls into the `c_dpi_aes`
  // reference implementation.

  // The ciphertext and authentication tag parts are compared in the same cycle
  // after a successful read of the AES data output register.

  logic out_cntr_en;
  assign out_cntr_en = ~shim_hld && (shim_req.addr == 32'(AES_DATA_OUT_0_OFFSET) ||
                                     shim_req.addr == 32'(AES_DATA_OUT_1_OFFSET) ||
                                     shim_req.addr == 32'(AES_DATA_OUT_2_OFFSET) ||
                                     shim_req.addr == 32'(AES_DATA_OUT_3_OFFSET)) ? 1'b1 : 1'b0;

  int out_cntr_d, out_cntr_q;
  always_comb begin
    out_cntr_d = out_cntr_q;
    if (out_cntr_en) begin
      out_cntr_d = out_cntr_q + 1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_cntr_q <= 0;
    end else begin
      out_cntr_q <= out_cntr_d;
    end
  end

  logic [255:0] c_dpi_key;
  logic [127:0] c_dpi_iv;
  logic [7:0]   c_dpi_pt [16];
  assign c_dpi_key = '{default: '0};
  assign c_dpi_iv  = '{default: '0};
  assign c_dpi_pt  = '{default: '0};

  logic [31:0][7:0] c_dpi_model_q;
  logic [7:0] c_dpi_ct [16];
  logic [3:0][3:0][7:0] c_dpi_tag;

  always_comb begin
    aes_model_dpi_pkg::c_dpi_aes_crypt_message(
      1'b1,      // Reference Implementation: OpenSSL/BoringSSL
      1'b0,      // Operation: Encryption
      AES_GCM,   // Mode: GCM
      c_dpi_iv,  // IV
      AES_128,   // Key Length: 128
      c_dpi_key, // Key
      c_dpi_pt,  // Data Input
      '0,        // AD Input: null
      '0,        // Tag Input: null
      c_dpi_ct,  // CT Output
      c_dpi_tag  // Tag Output
    );
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      c_dpi_model_q[31:16] <= aes_transpose(c_dpi_tag);
      for (int i = 0; i < 16; i++) begin
        c_dpi_model_q[i] <= c_dpi_ct[i];
      end
    end else if (out_cntr_en) begin
      for (int i = 0; i < 32; i++) begin
        // Rotate `c_dpi` output.
        c_dpi_model_q[i] <= c_dpi_model_q[(i+4)%32];
      end
    end
  end

  logic dpi_error;
  assign dpi_error = out_cntr_en && c_dpi_model_q[3:0] != shim_rdata ? 1'b1 : 1'b0;

  // We do not care about alerts in this testbench. Set them to constant values.
  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx;
  assign alert_rx[0].ping_p = 1'b0;
  assign alert_rx[0].ping_n = 1'b1;
  assign alert_rx[0].ack_p  = 1'b0;
  assign alert_rx[0].ack_n  = 1'b1;
  assign alert_rx[1].ping_p = 1'b0;
  assign alert_rx[1].ping_n = 1'b1;
  assign alert_rx[1].ack_p  = 1'b0;
  assign alert_rx[1].ack_n  = 1'b1;

  // Tie off unused signals.
  logic unused_signals;
  assign unused_signals = ^{alert_tx};

endmodule
