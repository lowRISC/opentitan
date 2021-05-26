// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src top level wrapper file

`include "prim_assert.sv"


module entropy_src
  import entropy_src_pkg::*;
  import entropy_src_reg_pkg::*;
#(
  parameter bit Stub = 1'b0,
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter int EsFifoDepth = 4
) (
  input logic clk_i,
  input logic rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // OTP Interface
  input  otp_ctrl_pkg::otp_en_t otp_en_entropy_src_fw_read_i,

  // RNG Interface
  output logic rng_fips_o,

  // Entropy Interface
  input  entropy_src_hw_if_req_t entropy_src_hw_if_i,
  output entropy_src_hw_if_rsp_t entropy_src_hw_if_o,

  // RNG Interface
  output entropy_src_rng_req_t entropy_src_rng_o,
  input  entropy_src_rng_rsp_t entropy_src_rng_i,

  // CSRNG Interface
  output cs_aes_halt_req_t cs_aes_halt_o,
  input  cs_aes_halt_rsp_t cs_aes_halt_i,

  // External Health Test Interface
  output entropy_src_xht_req_t entropy_src_xht_o,
  input  entropy_src_xht_rsp_t entropy_src_xht_i,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Interrupts
  output logic    intr_es_entropy_valid_o,
  output logic    intr_es_health_test_failed_o,
  output logic    intr_es_fatal_err_o
);

  import entropy_src_reg_pkg::*;

  // common signals
  entropy_src_hw2reg_t hw2reg;
  entropy_src_reg2hw_t reg2hw;
  logic [NumAlerts-1:0] alert_test;
  logic [NumAlerts-1:0] alert;

  // core signals
  logic core_rst_n;
  entropy_src_hw2reg_t core_hw2reg;
  entropy_src_hw_if_rsp_t core_entropy_hw_if;
  entropy_src_rng_req_t core_rng;
  cs_aes_halt_req_t core_aes_halt;
  entropy_src_xht_req_t core_xht;
  logic core_intr_es_entropy_valid;
  logic core_intr_es_health_test_failed;
  logic core_intr_es_fatal_err;
  logic [NumAlerts-1:0] core_alert_test;
  logic [NumAlerts-1:0] core_alert;

  //stub signals
  localparam int StubLfsrWidth = 64;
  localparam int Copies = CSRNG_BUS_WIDTH / StubLfsrWidth;
  entropy_src_hw2reg_t stub_hw2reg;
  entropy_src_hw_if_rsp_t stub_entropy_hw_if;
  logic stub_es_valid;
  logic [NumAlerts-1:0] stub_alert_test;
  logic [NumAlerts-1:0] stub_alert;
  logic [StubLfsrWidth-1:0] stub_lfsr_value;

  ///////////////////////////
  // Selecting between core and stub
  ///////////////////////////

  assign hw2reg                       = Stub ? stub_hw2reg        : core_hw2reg;
  assign core_rst_n                   = Stub ? '0                 : rst_ni;
  assign entropy_src_hw_if_o          = Stub ? stub_entropy_hw_if : core_entropy_hw_if;
  assign entropy_src_rng_o            = Stub ? '1                 : core_rng;
  assign cs_aes_halt_o                = Stub ? '0                 : core_aes_halt;
  assign entropy_src_xht_o            = Stub ? '0                 : core_xht;
  assign intr_es_entropy_valid_o      = Stub ? stub_es_valid      : core_intr_es_entropy_valid;
  assign intr_es_health_test_failed_o = Stub ? '0                 : core_intr_es_health_test_failed;
  assign intr_es_fatal_err_o          = Stub ? '0                 : core_intr_es_fatal_err;
  assign alert_test                   = Stub ? stub_alert_test    : core_alert_test;
  assign alert                        = Stub ? stub_alert         : core_alert;

  ///////////////////////////
  // core entropy operation
  ///////////////////////////

  entropy_src_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg(hw2reg),
    .intg_err_o(),
    .devmode_i(1'b1)
  );

  logic efuse_es_sw_reg_en;
  assign efuse_es_sw_reg_en = (otp_en_entropy_src_fw_read_i == otp_ctrl_pkg::Enabled);

  entropy_src_core #(
    .EsFifoDepth(EsFifoDepth)
  ) u_entropy_src_core (
    .clk_i,
    .rst_ni(core_rst_n),
    .reg2hw,
    .hw2reg(core_hw2reg),

    .efuse_es_sw_reg_en_i(efuse_es_sw_reg_en),
    .rng_fips_o,

    .entropy_src_hw_if_o(core_entropy_hw_if),
    .entropy_src_hw_if_i,

    .entropy_src_xht_o(core_xht),
    .entropy_src_xht_i,

    .entropy_src_rng_o(core_rng),
    .entropy_src_rng_i,

    .cs_aes_halt_o(core_aes_halt),
    .cs_aes_halt_i,

    .recov_alert_o(core_alert[0]),
    .fatal_alert_o(core_alert[1]),

    .recov_alert_test_o(core_alert_test[0]),
    .fatal_alert_test_o(core_alert_test[1]),

    .intr_es_entropy_valid_o(core_intr_es_entropy_valid),
    .intr_es_health_test_failed_o(core_intr_es_health_test_failed),
    .intr_es_fatal_err_o(core_intr_es_fatal_err)
  );

  ///////////////////////////
  // stub entropy operation
  ///////////////////////////

  assign stub_alert = '0;
  assign stub_alert_test = '0;
  assign stub_entropy_hw_if = '{
    es_ack:  '1,
    es_bits:  {Copies{stub_lfsr_value}},
    es_fips: '1
  };
  // once enabled, stub entropy is always available
  assign stub_es_valid = |reg2hw.conf.enable.q;

  if (Stub) begin : gen_stub_entropy_src

    logic seed_ld, lfsr_en;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        lfsr_en <= '0;
      end else begin
        lfsr_en <= |reg2hw.conf.enable.q;
      end
    end
    assign seed_ld = |reg2hw.conf.enable.q & !lfsr_en;

    prim_lfsr #(
      .LfsrDw(StubLfsrWidth),
      .StateOutDw(StubLfsrWidth)
    ) u_prim_lfsr (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .seed_en_i      (seed_ld),
      .seed_i         (StubLfsrWidth'(reg2hw.seed.q)),
      .lfsr_en_i      (lfsr_en),
      .entropy_i      ('0),
      .state_o        (stub_lfsr_value)
    );

    // hardwire hw2reg inputs
    always_comb begin
      stub_hw2reg = '0;

      // as long as enable is 1, do not allow registers to be written
      stub_hw2reg.regwen.d = ~|reg2hw.conf.enable.q;
      stub_hw2reg.fw_ov_rd_data.d = stub_lfsr_value[31:0];
      stub_hw2reg.fw_ov_fifo_sts.d = '1;
      stub_hw2reg.entropy_data.d = stub_lfsr_value[31:0];
      stub_hw2reg.debug_status.main_sm_idle.d = 1'b1;
      // need to move this to package so that it can be referenced
      stub_hw2reg.debug_status.main_sm_state.d = 8'b01110110;

      stub_hw2reg.intr_state.es_entropy_valid.de = |reg2hw.conf.enable.q;
      stub_hw2reg.intr_state.es_entropy_valid.d = 1'b1;

    end
  end else begin : gen_stub_tieoff
    assign stub_hw2reg = '0;
    assign stub_lfsr_value = '0;
  end

  ///////////////////////////
  // Alert generation
  ///////////////////////////
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alert[i]      ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // Outputs should have a known value after reset
  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)

  // Entropy Interface
  `ASSERT_KNOWN(EsHwIfEsAckKnownO_A, entropy_src_hw_if_o.es_ack)
  `ASSERT_KNOWN(EsHwIfEsBitsKnownO_A, entropy_src_hw_if_o.es_bits)
  `ASSERT_KNOWN(EsHwIfEsFipsKnownO_A, entropy_src_hw_if_o.es_fips)

  // RNG Interface
  `ASSERT_KNOWN(EsRngEnableKnownO_A, entropy_src_rng_o.rng_enable)

  // External Health Test Interface
  `ASSERT_KNOWN(EsXhtEntropyBitKnownO_A, entropy_src_xht_o.entropy_bit)
  `ASSERT_KNOWN(EsXhtEntropyBitValidKnownO_A, entropy_src_xht_o.entropy_bit_valid)
  `ASSERT_KNOWN(EsXhtClearKnownO_A, entropy_src_xht_o.clear)
  `ASSERT_KNOWN(EsXhtActiveKnownO_A, entropy_src_xht_o.active)
  `ASSERT_KNOWN(EsXhtThreshHiKnownO_A, entropy_src_xht_o.thresh_hi)
  `ASSERT_KNOWN(EsXhtThreshLoKnownO_A, entropy_src_xht_o.thresh_lo)
  `ASSERT_KNOWN(EsXhtWindowKnownO_A, entropy_src_xht_o.window)

  // Alerts
  `ASSERT_KNOWN(AlertTxKnownO_A, alert_tx_o)

  // Interrupts
  `ASSERT_KNOWN(IntrEsEntropyValidKnownO_A, intr_es_entropy_valid_o)
  `ASSERT_KNOWN(IntrEsHealthTestFailedKnownO_A, intr_es_health_test_failed_o)
  `ASSERT_KNOWN(IntrEsFifoErrKnownO_A, intr_es_fatal_err_o)

endmodule
