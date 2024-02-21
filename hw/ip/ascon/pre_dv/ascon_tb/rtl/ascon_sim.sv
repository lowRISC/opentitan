// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon simulation wrapper

module ascon_sim import ascon_pkg::*;
#(
  localparam int DONE_DELAY_CYCLES = 10
)
(
  input  clk_i,
  input  rst_ni,

  output test_done_o,
  output test_passed_o
);

  import ascon_reg_pkg::*;


  // Signals
  // Bus Interface
  tlul_pkg::tl_h2d_t tl_i;
  tlul_pkg::tl_d2h_t tl_o;
  tlul_pkg::tl_d2h_t tl_expected_response;


  logic stimulus_done;
  logic pop_stimulus;
  logic pop_response;

  // only pop new response if previous response was AccessAckData
  assign pop_response = tl_i.d_ready & tl_o.d_valid
                        & (tl_o.d_opcode == tlul_pkg::AccessAckData);
  assign pop_stimulus = tl_o.a_ready & tl_i.a_valid;

  ascon_tl_ul_stim g_ascon_tl_ul_stim (
    .clk_i,
    .rst_ni,
    .expected_tlul_resonse_o (tl_expected_response),
    .tlul_stimulus_o         (tl_i),
    .pop_next_stimulus_i     (pop_stimulus),
    .pop_next_response_i     (pop_response),
    .done_o                  (stimulus_done)
  );

  // latch simulation done_o:
  generate
    if (DONE_DELAY_CYCLES > 0) begin : gen_delay_logic
      logic delay_done_q[DONE_DELAY_CYCLES];
      for (genvar i = 1; i < DONE_DELAY_CYCLES; i++) begin : gen_done_delay
        always_ff @(posedge clk_i or negedge rst_ni) begin : reg_done_delay
          if (!rst_ni) begin
            delay_done_q[i] <= 1'b0;
          end else begin
            delay_done_q[i-1] <= delay_done_q[i];
          end
        end
      end
      assign delay_done_q[DONE_DELAY_CYCLES-1] = stimulus_done;
      assign test_done_o = delay_done_q[0];
    end else begin : gen_no_delay
      assign test_done_o = stimulus_done;
    end
  endgenerate

  // latch passed_o
  logic test_passed_q;
  logic current_test;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      test_passed_q <= 1'b1;
    end else if (pop_response) begin
      test_passed_q <= test_passed_q & current_test;
    end
  end

  assign test_passed_o = test_passed_q;
  assign current_test = (tl_o.d_data == tl_expected_response.d_data) ? 1'b1 : 1'b0;

  // All other interfaces are static for the moment

  // Entropy Interface
  logic edn_req;

  // Key Manager Interface
  keymgr_pkg::hw_key_req_t keymgr_key;

  // alerts
  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx, unused_alert_tx;


  // Key Manger Interface
  // Set a fixed sideload key for now.
  assign keymgr_key.valid  = 1'b1;
  assign keymgr_key.key[0][255:128] = 128'hFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF;
  assign keymgr_key.key[0][127:0]   = 128'hE5799080_2BF310C8_52640EDA_F7B0738E;
  assign keymgr_key.key[1][255:128] = 128'hFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF;
  assign keymgr_key.key[1][127:0]   = '0;

  // Entropy Interface
  // Use a counter to provide some entropy for visual inspection.
  logic [31:0] entropy_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_entropy
    if (!rst_ni) begin
      entropy_q <= 32'h12345678;
    end else if (edn_req) begin
      entropy_q <= entropy_q + 32'h1;
    end
  end

  // Alert Interface
  // Don't test alerts
  assign alert_rx[0].ping_p = 1'b0;
  assign alert_rx[0].ping_n = 1'b1;
  assign alert_rx[0].ack_p  = 1'b0;
  assign alert_rx[0].ack_n  = 1'b1;
  assign alert_rx[1].ping_p = 1'b0;
  assign alert_rx[1].ping_n = 1'b1;
  assign alert_rx[1].ack_p  = 1'b0;
  assign alert_rx[1].ack_n  = 1'b1;
  assign unused_alert_tx = alert_tx;

  // Instantiate top-level
  ascon u_ascon (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni  ( rst_ni                     ),
    .idle_o           (                            ),
    .lc_escalate_en_i ( lc_ctrl_pkg::Off           ),
    .clk_edn_i        ( clk_i                      ),
    .rst_edn_ni       ( rst_ni                     ),
    .edn_o            ( edn_req                    ),
    .edn_i            ( {edn_req, 1'b1, entropy_q} ),
    .keymgr_key_i     ( keymgr_key                 ),
    .tl_i,
    .tl_o,
    .alert_rx_i       ( alert_rx                   ),
    .alert_tx_o       ( alert_tx                   )
  );


endmodule
