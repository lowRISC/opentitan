// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for spid_jedec

module spid_jedec_tb;

  import spi_device_pkg::*;

  import spid_common::*;

  localparam time ClkPeriod = 10000; // 10ns
  localparam time SckPeriod = 14000; // 14ns

  localparam logic [7:0] ContinuousCode = 8'h AD;

  wire clk, rst_n;
  clk_rst_if main_clk (
    .clk,
    .rst_n
  );

  wire sck, sck_rst_n;
  clk_rst_if sck_clk (
    .clk   (sck),
    .rst_n (sck_rst_n)
  );

  spi_if sif(sck);

  virtual spi_if.tb  tb_sif  = sif.tb;
  virtual spi_if.dut dut_sif = sif.dut;

  logic [3:0] dut_sd_en, dut_sd;
  logic [3:0] tb_sd_en,  tb_sd;

  for (genvar i = 0 ; i < 4 ; i++) begin : g_dut_sif
    assign sif.sd_out[i] = dut_sd_en[i] ? dut_sd[i] : 1'b Z;
  end

  wire sck_en, gated_sck, gated_sck_inverted;

  assign gated_sck          = (sck_en) ? sck : 1'b 0;
  assign gated_sck_inverted = ~gated_sck;

  assign sck_en = ~sif.csb;

  logic rst_spi_n;
  assign rst_spi_n = sck_rst_n && ~sif.csb;

  sel_datapath_e dut_sel_dp;
  // Command info for Read Status
  // CmdReadStauts1, CmdReadStatus2, CmdReadStatus3
  logic [CmdInfoIdxW-1:0] cmd_info_idx;
  cmd_info_t cmd_info;

  // Status Signals
  logic sys_status_we;
  logic [23:0] sys_status_in, sys_status_out;

  logic busy_set; // SCK

  // JEDEC Signals
  jedec_cfg_t jedec_id;

  spi_mode_e spi_mode;

  logic s2p_valid;
  logic [7:0] s2p_data;

  initial begin
    sck_clk.set_period_ps(SckPeriod);
    sck_clk.set_active();

    main_clk.set_period_ps(ClkPeriod);
    main_clk.set_active();

    sif.csb = 1'b 1;

    sck_clk.apply_reset();
    main_clk.apply_reset();

    fork
      begin
        #20us
        $display("TEST TIMED OUT!!");
        $finish();
      end
      host();
      sw();
    join_any

    $finish();
  end

  static task host();
    logic [23:0] jedec_id;

    // Initial config
    spi_mode = FlashMode;

    repeat(10) @(sck_clk.cbn);

    // Expect 5 continuous codes and jedec ID
    spiflash_readjedec(tb_sif, CmdJedecId, 8'h 5, ContinuousCode, jedec_id);

    $display("SPI Flash Read JEDEC ID Tested!!:");
  endtask : host

  static task sw();
    // Initial config
    jedec_id = '{
      num_cc:     8'h 5        ,
      cc:        ContinuousCode,
      jedec_id:   8'h BE       ,
      device_id: 16'h A55A
    };

    forever @(posedge clk); // Wait host transaction done

  endtask : sw

  // CSb pulse
  logic csb_sckin_sync_d, csb_sckin_sync_q, csb_asserted_pulse_sckin;
  prim_flop_2sync #(
    .Width      (1),
    .ResetValue (1'b 1)
  ) u_csb_sckin_sync (
    .clk_i (gated_sck),
    .rst_ni(rst_spi_n), //Use CSb as a reset
    .d_i (1'b 0),
    .q_o (csb_sckin_sync_d)
  );
  always_ff @(posedge gated_sck or negedge rst_spi_n) begin
    if (!rst_spi_n) csb_sckin_sync_q <= 1'b 1;
    else            csb_sckin_sync_q <= csb_sckin_sync_d;
  end

  assign csb_asserted_pulse_sckin = csb_sckin_sync_q && !csb_sckin_sync_d;

  logic p2s_valid, p2s_sent;
  logic [7:0] p2s_data;

  io_mode_e dut_iomode, s2p_iomode;

  spid_jedec dut (
    .clk_i  (gated_sck),
    .rst_ni (rst_spi_n),

    .clk_out_i (gated_sck_inverted),

    .inclk_csb_asserted_pulse_i (csb_asserted_pulse_sckin),

    .sys_jedec_i (jedec_id),

    .io_mode_o (dut_iomode),

    .sel_dp_i       (dut_sel_dp  ),
    .cmd_info_i     (cmd_info    ),
    .cmd_info_idx_i (cmd_info_idx),

    .outclk_p2s_valid_o (p2s_valid),
    .outclk_p2s_byte_o  (p2s_data ),
    .outclk_p2s_sent_i  (p2s_sent )
  );

  spi_cmdparse cmdparse (
    .clk_i  (gated_sck),
    .rst_ni (rst_spi_n),

    .data_valid_i (s2p_valid),
    .data_i       (s2p_data ),

    .spi_mode_i   (spi_mode),

    .cmd_info_i   (spid_common::CmdInfo),

    .io_mode_o    (s2p_iomode),

    .sel_dp_o       (dut_sel_dp),
    .cmd_info_o     (cmd_info),
    .cmd_info_idx_o (cmd_info_idx),

    .cmd_config_req_o (),
    .cmd_config_idx_o ()
  );

  spi_s2p s2p (
    .clk_i  (gated_sck),
    .rst_ni (rst_spi_n),

    .s_i    (sif.sd_in),

    .data_valid_o (s2p_valid),
    .data_o       (s2p_data),
    .bitcnt_o     (),

    .order_i      (1'b 0),
    .io_mode_i    (s2p_iomode)
  );

  spi_p2s p2s (
    .clk_i  (gated_sck_inverted),
    .rst_ni (rst_spi_n),

    .data_valid_i (p2s_valid),
    .data_i       (p2s_data),
    .data_sent_o  (p2s_sent),

    .csb_i        (sif.csb),
    .s_en_o       (dut_sd_en),
    .s_o          (dut_sd),

    .cpha_i       (1'b 0),

    .order_i      (1'b 0),

    .io_mode_i    (dut_iomode)
  );

endmodule : spid_jedec_tb
