// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC-SHA3

`include "prim_assert.sv"

module kmac
  import kmac_pkg::*;
(
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

`ifndef KMAC_STANDALONE
  input  keymgr_pkg::hw_key_req_t    keymgr_key_i,
  input  keymgr_pkg::kmac_data_req_t keymgr_data_i,
  output keymgr_pkg::kmac_data_rsp_t keymgr_data_o,
`endif // KMAC_STANDALONE

  output logic intr_kmac_done_o,
  output logic intr_fifo_empty_o,
  output logic intr_kmac_err_o,

  // alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o

);

  import kmac_reg_pkg::*;

  kmac_reg2hw_t reg2hw;
  kmac_hw2reg_t hw2reg;

  logic fifo_wvalid, fifo_wready, fifo_rvalid, fifo_rready;
  logic [63:0] fifo_wdata, fifo_rdata;

  tlul_pkg::tl_h2d_t tl_win_h2d [2]; // DIGEST [0] / MSG_FIFO [1]
  tlul_pkg::tl_d2h_t tl_win_d2h [2]; // DIGEST [0] / MSG_FIFO [1]

  // Alert ====================================================================
  logic [NumAlerts-1:0] alerts;
  for (genvar i = 0 ; i < NumAlerts; i++) begin: alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i])
    ) i_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_i    ( alerts[i]     ),
      .alert_rx_i ( alert_rx_i[i] ),
      .alert_tx_o ( alert_tx_o[i] )
    );
  end : alert_tx

  assign alerts[0] = reg2hw.alert_test.sram_uncorrectable.qe &
                     reg2hw.alert_test.sram_uncorrectable.q;
  assign alerts[1] = reg2hw.alert_test.data_parity.qe &
                     reg2hw.alert_test.data_parity.q;

  // RAM instance =============================================================
  logic packer_wvalid, packer_wready, packer_rvalid, packer_rready;
  logic [31:0] packer_wdata;
  logic [31:0] packer_wmask;
  logic [63:0] packer_rdata;
  logic [63:0] packer_rmask;

  // TODO: Temporary adapter, need to remove later
  logic [3:0] adapter_be;
  tlul_adapter_reg #(
    .RegAw (12) // 2kB
  ) u_fifo_adapter (
    .clk_i,
    .rst_ni,

    .tl_i (tl_win_h2d[1]),
    .tl_o (tl_win_d2h[1]),

    .re_o    (),
    .we_o    (packer_wvalid), // consider write only
    .addr_o  (), // doesn't care
    .wdata_o (packer_wdata),
    .be_o    (adapter_be),
    .rdata_i (32'h0),
    .error_i (1'b0)
  );

  always_comb begin
    for (int i = 0 ; i < 3 ; i++) begin
      packer_wmask[8*i+:8] = {8{adapter_be[i]}};
    end
  end

  prim_packer #(
    .InW   (32),
    .OutW  (64)
  ) u_packer (
    .clk_i,
    .rst_ni,
    .valid_i      (packer_wvalid),
    .data_i       (packer_wdata ),
    .mask_i       (packer_wmask ),
    .ready_o      (packer_wready),
    .valid_o      (packer_rvalid),
    .data_o       (packer_rdata ),
    .mask_o       (packer_rmask ),
    .ready_i      (packer_rready),

    .flush_i      (reg2hw.cmd.process.q & reg2hw.cmd.process.qe),
    .flush_done_o ()
  );

  assign fifo_wvalid = packer_rvalid;
  assign packer_rready = fifo_wready;
  assign fifo_wdata = packer_rdata;
  // TODO: Handle mask


  prim_fifo_sync #(
    .Depth (26),
    .Width (64)
  ) u_msg_fifo (
    .clk_i,
    .rst_ni,
    .clr_i      (1'b0),
    .wvalid     (fifo_wvalid),
    .wready     (fifo_wready),
    .wdata      (fifo_wdata ),
    .rvalid     (fifo_rvalid),
    .rready     (fifo_rready),
    .rdata      (fifo_rdata ),
    .depth      ()
  );
  // Random Gate Gen ==========================================================
  prim_gate_gen #(
    .DataWidth (32),
    .NumGates  (30000)
  )u_random_gates (
    .clk_i,
    .rst_ni,
    .valid_i (reg2hw.dummy.qe),
    .data_i  (reg2hw.dummy.q),
    .data_o  (hw2reg.dummy.d),
    .valid_o (hw2reg.dummy.de)
  );

  // Register =================================================================
  kmac_reg_top i_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .tl_win_o (tl_win_h2d),
    .tl_win_i (tl_win_d2h),

    .reg2hw,
    .hw2reg,

    .devmode_i (1'b0)
  );

  // Dummy connection =========================================================
  assign hw2reg.cfg = '0;
  assign hw2reg.status = '1;
  // TODO: Connect interface from keymgr to dummy gates

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      keymgr_data_o <= '{
        ready: 1'b1,
        default: '0
      };
    end else if (keymgr_data_i.valid) begin
      keymgr_data_o.done <= 1'b1;
      keymgr_data_o.digest_share0 <= keymgr_key_i.key_share0 ^ keymgr_data_i.data;
      keymgr_data_o.digest_share1 <= keymgr_key_i.key_share1 ^ keymgr_data_i.data;
    end
  end

endmodule

