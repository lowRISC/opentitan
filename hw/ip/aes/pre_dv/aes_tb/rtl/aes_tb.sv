// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module aes_tb
  import tlul_pkg::*;
  import aes_pkg::*;
  import aes_reg_pkg::*;
  import aes_tb_pkg::*;

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
  localparam bit          DelayerEnable          = 0,
  localparam bit          ShimEnable             = 1
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

  logic         bus_done;
  logic         bus_pop;
  bus_request_t bus_req;

  logic                      bus_wait;
  logic                      bus_error;
  logic [top_pkg::TL_DW-1:0] bus_rdata;

  logic error;
  logic c_dpi_data_error;
  logic c_dpi_tag_error;
  assign error = bus_error | c_dpi_data_error | c_dpi_tag_error;

  logic test_passed_q;
  logic test_done_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      test_passed_q <= 1'b1;
      test_done_q   <= 1'b0;
    end else if (bus_done || error) begin
      test_passed_q <= ~error;
      test_done_q   <= 1'b1;
    end
  end
  assign test_done_o = test_done_q;
  assign test_passed_o = test_passed_q;

  // The AES block is run in automatic mode, which means the status register has to be polled in
  // order to check whether an operation has finished. A convenient side-effect of this is that it
  // will generate a large number of TLUL requests, which in combination with the delayer serves as
  // a good stress test of the bus.
  //
  // Reads of the AES status registers are repeated (without popping a new request from the stack)
  // until it matches the `bus_req.mask`. Such a stall can occur when the `IDLE` bit needs to be
  // asserted before the computation can advance.
  logic poll;
  assign poll = ~bus_wait
      & (bus_req.addr == 32'(AES_STATUS_OFFSET))
      & ~|(bus_rdata & bus_req.mask);
  assign bus_pop = (~bus_wait & ~poll) | bus_req.c_dpi_load;

  aes_mode_e aes_mode_q;
  gcm_phase_e gcm_phase_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      gcm_phase_q <= '0;
      aes_mode_q <= '0;
    end else if (bus_req.c_dpi_load) begin
      gcm_phase_q <= '0;
      aes_mode_q <= bus_req.c_dpi_input.mode;
    end else if (bus_req.addr == 32'(AES_CTRL_GCM_SHADOWED_OFFSET)) begin
      gcm_phase_q <= bus_req.wdata[5:0];
    end
  end

  aes_tb_reqs u_aes_tb_reqs (
    .clk_i         ( clk_i    ),
    .rst_ni        ( rst_ni   ),
    .pop_req_i     ( bus_pop  ),
    .req_o         ( bus_req  ),
    .done_o        ( bus_done )
  );

  // Every request that is not a `c_dpi_load` counts as a valid bus access.
  logic bus_en;
  assign bus_en = ~bus_req.c_dpi_load;

  // The shim converts inputs from the valid-hold protocol into TLUL requests.
  if (ShimEnable) begin : gen_tlul_adapter_shim
    tlul_adapter_shim #(
      .EnableDataIntgGen      ( EnableDataIntgGen      ),
      .EnableRspDataIntgCheck ( EnableRspDataIntgCheck )
    ) u_tlul_adapter_shim (
      .clk_i   ( clk_i                  ),
      .rst_ni  ( rst_ni                 ),
      .tl_i    ( tl_d2h_delayed         ),
      .tl_o    ( tl_h2d                 ),
      .dv_i    ( bus_en                 ),
      .addr_i  ( bus_req.addr           ),
      .write_i ( bus_req.write          ),
      .wdata_i ( bus_req.wdata          ),
      .wstrb_i ( 4'b1111                ),
      .size_i  ( 3'b010                 ),
      .hld_o   ( bus_wait               ),
      .rdata_o ( bus_rdata              ),
      .error_o ( bus_error              ),
      .last_i  ( 1'b0                   ),
      .user_i  ( 32'(TL_A_USER_DEFAULT) ),
      .id_i    ( '0                     )
    );
  end else begin : gen_tlul_adapter
    tlul_adapter_tb_reqs #(
      .EnableDataIntgGen      ( EnableDataIntgGen      ),
      .EnableRspDataIntgCheck ( EnableRspDataIntgCheck )
    ) u_tlul_adapter_tb_reqs (
      .clk_i        ( clk_i          ),
      .rst_ni       ( rst_ni         ),
      .tl_i         ( tl_d2h_delayed ),
      .tl_o         ( tl_h2d         ),
      .en_i    ( bus_en        ),
      .wait_o  ( bus_wait      ),
      .addr_i  ( bus_req.addr  ),
      .write_i ( bus_req.write ),
      .wdata_i ( bus_req.wdata ),
      .rdata_o ( bus_rdata     ),
      .error_o ( bus_error     )
    );
  end

  tlul_delayer #(
    .DelayerEnable ( DelayerEnable )
  ) u_tlul_delayer (
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

  // This is a sanity check verifying whether the AES Block has correctly computed the
  // plaintext/ciphertext and tag (in the case of AES-GCM) by cross-checking the hardware output with
  // the `c_dpi` model that interfaces with the OpenSSL/BoringSSL cryptographic library.

  logic check_out;
  logic check_data;
  logic check_tag;

  assign check_out = ~bus_wait && (bus_req.addr == 32'(AES_DATA_OUT_0_OFFSET) ||
                                   bus_req.addr == 32'(AES_DATA_OUT_1_OFFSET) ||
                                   bus_req.addr == 32'(AES_DATA_OUT_2_OFFSET) ||
                                   bus_req.addr == 32'(AES_DATA_OUT_3_OFFSET)) ? 1'b1 : 1'b0;

  assign check_data = check_out && (aes_mode_q != AES_GCM || gcm_phase_q == GCM_TEXT) ? 1'b1 : 1'b0;
  assign check_tag  = check_out && (gcm_phase_q == GCM_TAG)  ? 1'b1 : 1'b0;

  // GCM allows incomplete plaintext/ciphertext blocks which need to be masked in order to establish
  // correctness with the `c_dpi` model. We do this by initializing a counter to the number of data
  // bytes and decrementing it whenever 32 data bits from the AES block arrive. The value of the
  // counter steers a mask that is applied to both the AES block and the `c_dpi` model block. The
  // counter is reset for every `c_dpi_load`.

  int data_cntr_d, data_cntr_q;
  assign data_cntr_d = bus_req.c_dpi_load ? `DATA_LENGTH :
                       check_data         ? (data_cntr_q >= 4 ? data_cntr_q - 4 : 0) : data_cntr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_cntr_q <= `DATA_LENGTH;
    end else begin
      data_cntr_q <= data_cntr_d;
    end
  end

  logic [31:0] data_mask;
  assign data_mask = data_cntr_q >= 4 ? 32'hffff_ffff :
                     data_cntr_q == 3 ? 32'h00ff_ffff :
                     data_cntr_q == 2 ? 32'h0000_ffff :
                     data_cntr_q == 1 ? 32'h0000_00ff : '0;

  logic [31:0] c_dpi_data, c_dpi_tag;
  aes_tb_c_dpi #(
    .ADLength   ( `AD_LENGTH   ),
    .DataLength ( `DATA_LENGTH )
  ) u_aes_tb_c_dpi (
     .clk_i               ( clk_i               ),
     .rst_ni              ( rst_ni              ),
     .c_dpi_input_i       ( bus_req.c_dpi_input ),
     .c_dpi_load_i        ( bus_req.c_dpi_load  ),
     .c_dpi_rotate_data_i ( check_data          ),
     .c_dpi_rotate_tag_i  ( check_tag           ),
     .c_dpi_data_o        ( c_dpi_data          ),
     .c_dpi_tag_o         ( c_dpi_tag           )
  );

  assign c_dpi_data_error = check_data &&
                            (c_dpi_data & data_mask) != (bus_rdata & data_mask) ? 1'b1 : 1'b0;
  assign c_dpi_tag_error  = check_tag && (c_dpi_tag != bus_rdata) ? 1'b1 : 1'b0;

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
