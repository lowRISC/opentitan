// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for spid_status

module spid_status_tb;

  import spi_device_pkg::*;

  import spid_common::*;

  localparam time ClkPeriod = 10000; // 10ns
  localparam time SckPeriod = 14000; // 14ns

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

  logic sys_status_we;
  logic [23:0] sys_status_in, sys_status_out;

  logic busy_set; // SCK

  spi_mode_e spi_mode;

  logic      s2p_valid;
  spi_byte_t s2p_data;

  // wel_test_complete: Host triggers when wren/wrdi sent
  // wel_update_done: SW triggers when update Status after wel_test
  event wel_test_complete, wel_update_done;

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

  task host();
    spi_data_t data;

    // Initial config
    spi_mode = FlashMode;

    repeat(10) @(sck_clk.cbn);

    spiflash_readstatus(tb_sif, 8'h 05, data);

    repeat(10) @(sck_clk.cbn);

    spiflash_readstatus(tb_sif, 8'h 35, data);

    repeat(10) @(sck_clk.cbn);

    spiflash_readstatus(tb_sif, 8'h 15, data);

    $display("SPI Flash Read Status Tested!!");

    $display("WREN/ WRDI tests");
    spiflash_wren(tb_sif, 8'h 06); // WREN

    repeat(20) @(sck_clk.cbn);

    // Read back and check
    spiflash_readstatus(tb_sif, 8'h 05, data);

    assert(data[1] == 1'b 1);

    repeat(20) @(sck_clk.cbn);

    spiflash_wrdi(tb_sif, 8'h 04); // WRDI

    repeat(20) @(sck_clk.cbn);

    // Read back and check
    spiflash_readstatus(tb_sif, 8'h 05, data);

    assert(data[1] == 1'b 0);

    repeat(20) @(sck_clk.cbn);
    ->wel_test_complete;

    @(wel_update_done);

    // Expect SW to set WEL again.
    // The SW request is comitted after a SPI transaction is received.
    // Sending read status command but expect WEL still 0.
    // Then next Read Status will return the correct value (WEL == 1)

    @(sck_clk.cbn);
    // This should return 0 for WEL
    spiflash_readstatus(tb_sif, 8'h 05, data);
    assert(data[1] == 1'b 0);
    repeat(20) @(sck_clk.cbn);

    // This should return 1 for WEL
    spiflash_readstatus(tb_sif, 8'h 05, data);

    assert(data[1] == 1'b 1);
    repeat(20) @(sck_clk.cbn);


    $display("TEST PASSED CHECKS");
  endtask : host

  task sw();
    // Initial config
    busy_set = 1'b 0;
    sys_status_we = 1'b 0;
    sys_status_in = 24'h 0;

    repeat (5) @(posedge clk);

    sys_status_we = 1'b 1;
    sys_status_in = 24'h AD_BEEF;

    @(posedge clk);
    sys_status_we = 1'b 0;

    @(wel_test_complete);

    // Host has issued WREN then WRDI then read back the STATUS and checked if
    // HW updates the value correctly.
    // Now, SW reverts WEL bit (to 1), then informs host system to read back
    // the STATUS

    @(posedge clk);

    sys_status_we = 1'b 1;
    sys_status_in = 24'h 0A_BC_D2; // Set WEL
    @(posedge clk);
    sys_status_we = 1'b 0;

    repeat (10) @(posedge clk);

    ->wel_update_done;

    forever @(posedge clk); // Wait host transaction done

  endtask : sw

  logic p2s_valid, p2s_sent;
  logic [7:0] p2s_data;

  io_mode_e dut_iomode, s2p_iomode;

  logic sck_we_set, sck_we_clr;

  spid_status dut (
    .clk_i  (gated_sck),
    .rst_ni (rst_spi_n),

    .clk_out_i (gated_sck_inverted),

    .clk_csb_i (sif.csb),

    .sys_clk_i  (clk),
    .sys_rst_ni (rst_n),

    .sys_csb_deasserted_pulse_i (sys_csb_deasserted_pulse), // TODO

    .sys_status_we_i (sys_status_we ),
    .sys_status_i    (sys_status_in ),
    .sys_status_o    (sys_status_out),

    .sel_dp_i       (dut_sel_dp  ),
    .cmd_info_i     (cmd_info    ),
    .cmd_info_idx_i (cmd_info_idx),

    .outclk_p2s_valid_o (p2s_valid),
    .outclk_p2s_byte_o  (p2s_data ),
    .outclk_p2s_sent_i  (p2s_sent ),

    .io_mode_o   (dut_iomode),

    .inclk_busy_set_i  (busy_set), // SCK domain

    .inclk_we_set_i (sck_we_set),
    .inclk_we_clr_i (sck_we_clr),

    .csb_busy_broadcast_o () // SCK domain
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

    // CFG: Intercept
    .cfg_intercept_en_status_i (1'b 1),
    .cfg_intercept_en_jedec_i  (1'b 1),
    .cfg_intercept_en_sfdp_i   (1'b 1),

    // Intercept assumed
    .intercept_status_o (),
    .intercept_jedec_o  (),
    .intercept_sfdp_o   (),

    .cmd_config_req_o (),
    .cmd_config_idx_o ()
  );

  assign sck_we_set = (dut_sel_dp == DpWrEn);
  assign sck_we_clr = (dut_sel_dp == DpWrDi);

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

endmodule : spid_status_tb
