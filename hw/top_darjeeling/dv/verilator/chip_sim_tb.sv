// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module chip_sim_tb (
  // Clock and Reset
  input clk_i,
  input rst_ni
);

  logic [31:0]  cio_gpio_p2d, cio_gpio_d2p, cio_gpio_en_d2p;
  logic [31:0]  cio_gpio_pull_en, cio_gpio_pull_select;
  logic cio_uart_rx_p2d, cio_uart_tx_d2p, cio_uart_tx_en_d2p;

  logic cio_spi_device_sck_p2d, cio_spi_device_csb_p2d;
  logic cio_spi_device_sdi_p2d;
  logic cio_spi_device_sdo_d2p, cio_spi_device_sdo_en_d2p;

  logic cio_jtag_tck;
  logic cio_jtag_tms;
  logic cio_jtag_trst_n;
  logic cio_jtag_tdi;
  logic cio_jtag_tdo;

  chip_darjeeling_verilator u_dut (
    .clk_i,
    .rst_ni,

    // communication with GPIO
    .cio_gpio_p2d_i(cio_gpio_p2d),
    .cio_gpio_d2p_o(cio_gpio_d2p),
    .cio_gpio_en_d2p_o(cio_gpio_en_d2p),
    .cio_gpio_pull_en_o(cio_gpio_pull_en),
    .cio_gpio_pull_select_o(cio_gpio_pull_select),

    // communication with UART
    .cio_uart_rx_p2d_i(cio_uart_rx_p2d),
    .cio_uart_tx_d2p_o(cio_uart_tx_d2p),

    // communication with SPI
    .cio_spi_device_sck_p2d_i(cio_spi_device_sck_p2d),
    .cio_spi_device_csb_p2d_i(cio_spi_device_csb_p2d),
    .cio_spi_device_sdi_p2d_i(cio_spi_device_sdi_p2d),
    .cio_spi_device_sdo_d2p_o(cio_spi_device_sdo_d2p),
    .cio_spi_device_sdo_en_d2p_o(cio_spi_device_sdo_en_d2p),

    // communication with JTAG
    .cio_jtag_tck_i(cio_jtag_tck),
    .cio_jtag_tms_i(cio_jtag_tms),
    .cio_jtag_trst_ni(cio_jtag_trst_n),
    .cio_jtag_tdi_i(cio_jtag_tdi),
    .cio_jtag_tdo_o(cio_jtag_tdo)
  );

  // GPIO DPI
  gpiodpi #(.N_GPIO(32)) u_gpiodpi (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .gpio_p2d   (cio_gpio_p2d),
    .gpio_d2p   (cio_gpio_d2p),
    .gpio_en_d2p(cio_gpio_en_d2p),
    .gpio_pull_en(cio_gpio_pull_en),
    .gpio_pull_sel(cio_gpio_pull_select)
  );

  // UART DPI
  // The baud rate set to match FPGA implementation; the frequency is "artificial". Both baud rate
  // frequency must match the settings used in the on-chip software at
  // `sw/top_darjeeling/sw/device/arch/device_sim_verilator.c`.
  uartdpi #(
    .BAUD('d7_200),
    .FREQ('d500_000)
  ) u_uart (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .tx_o   (cio_uart_rx_p2d),
    .rx_i   (cio_uart_tx_d2p)
  );

  // OpenOCD JTAG DPI (to rv_dm and lc_ctrl)
  jtagdpi u_jtagdpi (
    .clk_i,
    .rst_ni,

    .jtag_tck    (cio_jtag_tck),
    .jtag_tms    (cio_jtag_tms),
    .jtag_tdi    (cio_jtag_tdi),
    .jtag_tdo    (cio_jtag_tdo),
    .jtag_trst_n (cio_jtag_trst_n),
    .jtag_srst_n ()
  );

  // SPI DPI
  spidpi u_spi (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .spi_device_sck_o     (cio_spi_device_sck_p2d),
    .spi_device_csb_o     (cio_spi_device_csb_p2d),
    .spi_device_sdi_o     (cio_spi_device_sdi_p2d),
    .spi_device_sdo_i     (cio_spi_device_sdo_d2p),
    .spi_device_sdo_en_i  (cio_spi_device_sdo_en_d2p)
  );

  `define RV_CORE_IBEX      u_dut.top_darjeeling.u_rv_core_ibex
  `define SIM_SRAM_IF       u_sim_sram.u_sim_sram_if

  // Detect SW test termination.
  sim_sram u_sim_sram (
    .clk_i    (`RV_CORE_IBEX.clk_i),
    .rst_ni   (`RV_CORE_IBEX.rst_ni),
    .tl_in_i  (tlul_pkg::tl_h2d_t'(`RV_CORE_IBEX.u_tlul_req_buf.out_o)),
    .tl_in_o  (),
    .tl_out_o (),
    .tl_out_i ()

  );

  // Connect the sim SRAM directly inside rv_core_ibex.
  assign `RV_CORE_IBEX.tl_win_d2h = u_sim_sram.tl_in_o;

  // Instantiate the SW test status interface & connect signals from sim_sram_if instance
  // instantiated inside sim_sram. Bind would have worked nicely here, but Verilator segfaults
  // when trace is enabled (#3951).
  sw_test_status_if u_sw_test_status_if (
    .clk_i    (`SIM_SRAM_IF.clk_i),
    .rst_ni   (`SIM_SRAM_IF.rst_ni),
    .fetch_en (1'b0),
    .wr_valid (`SIM_SRAM_IF.wr_valid),
    .addr     (`SIM_SRAM_IF.tl_h2d.a_address),
    .data     (`SIM_SRAM_IF.tl_h2d.a_data[15:0])
  );

  // Set the start address of the simulation SRAM.
  // Use offset 0 within the sim SRAM for SW test status indication.
  initial begin
    `SIM_SRAM_IF.start_addr = `VERILATOR_TEST_STATUS_ADDR;
    u_sw_test_status_if.sw_test_status_addr = `SIM_SRAM_IF.start_addr;
  end

  always @(posedge clk_i) begin
    if (u_sw_test_status_if.sw_test_done) begin
      $display("Verilator sim termination requested");
      $display("Your simulation wrote to 0x%h", u_sw_test_status_if.sw_test_status_addr);
      dv_test_status_pkg::dv_test_status(u_sw_test_status_if.sw_test_passed);
      $finish;
    end
  end

  `undef RV_CORE_IBEX
  `undef SIM_SRAM_IF


endmodule // chip_sim_tb
