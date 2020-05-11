// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni
);

  logic cio_jtag_tck, cio_jtag_tms, cio_jtag_tdi, cio_jtag_tdo;
  logic cio_jtag_trst_n, cio_jtag_srst_n;

  logic [31:0]  cio_gpio_p2d, cio_gpio_d2p, cio_gpio_en_d2p;
  logic cio_uart_rx_p2d, cio_uart_tx_d2p, cio_uart_tx_en_d2p;

  logic cio_spi_device_sck_p2d, cio_spi_device_csb_p2d;
  logic cio_spi_device_mosi_p2d;
  logic cio_spi_device_miso_d2p, cio_spi_device_miso_en_d2p;

  logic cio_usbdev_sense_p2d;
  logic cio_usbdev_se0_d2p, cio_usbdev_se0_en_d2p;
  logic cio_usbdev_dp_pullup_d2p, cio_usbdev_dp_pullup_en_d2p;
  logic cio_usbdev_dn_pullup_d2p, cio_usbdev_dn_pullup_en_d2p;
  logic cio_usbdev_tx_mode_se_d2p, cio_usbdev_tx_mode_se_en_d2p;
  logic cio_usbdev_suspend_d2p, cio_usbdev_suspend_en_d2p;
  logic cio_usbdev_d_p2d, cio_usbdev_d_d2p, cio_usbdev_d_en_d2p;
  logic cio_usbdev_dp_p2d, cio_usbdev_dp_d2p, cio_usbdev_dp_en_d2p;
  logic cio_usbdev_dn_p2d, cio_usbdev_dn_d2p, cio_usbdev_dn_en_d2p;

  logic IO_JTCK, IO_JTMS, IO_JTRST_N, IO_JTDI, IO_JTDO;

  // TODO: instantiate padring and route these signals through that module
  logic [14:0] dio_in;
  logic [14:0] dio_out;
  logic [14:0] dio_oe;

  assign dio_in = {cio_spi_device_sck_p2d,
                   cio_spi_device_csb_p2d,
                   cio_spi_device_mosi_p2d,
                   1'b0,
                   cio_uart_rx_p2d,
                   1'b0,
                   cio_usbdev_sense_p2d,
                   1'b0,
                   1'b0,
                   1'b0,
                   1'b0,
                   1'b0,
                   cio_usbdev_d_p2d,
                   cio_usbdev_dp_p2d,
                   cio_usbdev_dn_p2d};

  assign cio_usbdev_dn_d2p = dio_out[0];
  assign cio_usbdev_dp_d2p = dio_out[1];
  assign cio_usbdev_d_d2p  = dio_out[2];
  assign cio_usbdev_suspend_d2p = dio_out[3];
  assign cio_usbdev_tx_mode_se_d2p = dio_out[4];
  assign cio_usbdev_dn_pullup_d2p = dio_out[5];
  assign cio_usbdev_dp_pullup_d2p = dio_out[6];
  assign cio_usbdev_se0_d2p = dio_out[7];
  assign cio_uart_tx_d2p = dio_out[9];
  assign cio_spi_device_miso_d2p = dio_out[11];

  assign cio_usbdev_dn_en_d2p = dio_oe[0];
  assign cio_usbdev_dp_en_d2p = dio_oe[1];
  assign cio_usbdev_d_en_d2p  = dio_oe[2];
  assign cio_usbdev_suspend_en_d2p = dio_oe[3];
  assign cio_usbdev_tx_mode_se_en_d2p = dio_oe[4];
  assign cio_usbdev_dn_pullup_en_d2p = dio_oe[5];
  assign cio_usbdev_dp_pullup_en_d2p = dio_oe[6];
  assign cio_usbdev_se0_en_d2p = dio_oe[7];
  assign cio_uart_tx_en_d2p = dio_oe[9];
  assign cio_spi_device_miso_en_d2p = dio_oe[11];

  // Top-level design
  top_earlgrey top_earlgrey (
    .clk_i                      (clk_i),
    .rst_ni                     (rst_ni),
    .clk_io_i                   (clk_i),
    .clk_usb_i                  (clk_i),
    .clk_aon_i                  (clk_i),

    .jtag_tck_i                 (cio_jtag_tck),
    .jtag_tms_i                 (cio_jtag_tms),
    .jtag_trst_ni               (cio_jtag_trst_n),
    .jtag_tdi_i                 (cio_jtag_tdi),
    .jtag_tdo_o                 (cio_jtag_tdo),

    // Multiplexed I/O
    .mio_in_i                   (cio_gpio_p2d),
    .mio_out_o                  (cio_gpio_d2p),
    .mio_oe_o                   (cio_gpio_en_d2p),

    // Dedicated I/O
    .dio_in_i                   (dio_in),
    .dio_out_o                  (dio_out),
    .dio_oe_o                   (dio_oe),

    // Pad attributes
    .mio_attr_o                 ( ),
    .dio_attr_o                 ( ),

    .scanmode_i                 (1'b0)
  );

  // GPIO DPI
  gpiodpi #(.N_GPIO(32)) u_gpiodpi (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .gpio_p2d   (cio_gpio_p2d),
    .gpio_d2p   (cio_gpio_d2p),
    .gpio_en_d2p(cio_gpio_en_d2p)
  );

  // UART DPI
  // The baud rate set to match FPGA implementation; the frequency is
  // "artificial".
  // Both baud rate and frequency must match the settings used in the on-chip
  // software.
  uartdpi #(
    .BAUD('d9_600),
    .FREQ('d500_000)
  ) u_uart (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .tx_o   (cio_uart_rx_p2d),
    .rx_i   (cio_uart_tx_d2p)
  );

`ifdef DMIDirectTAP
  // OpenOCD direct DMI TAP
  bind rv_dm dmidpi u_dmidpi (
    .clk_i,
    .rst_ni,
    .dmi_req_valid,
    .dmi_req_ready,
    .dmi_req_addr   (dmi_req.addr),
    .dmi_req_op     (dmi_req.op),
    .dmi_req_data   (dmi_req.data),
    .dmi_rsp_valid,
    .dmi_rsp_ready,
    .dmi_rsp_data   (dmi_rsp.data),
    .dmi_rsp_resp   (dmi_rsp.resp),
    .dmi_rst_n      (dmi_rst_n)
  );
`else
  // JTAG DPI for OpenOCD
  jtagdpi u_jtagdpi (
    .clk_i,
    .rst_ni,

    .jtag_tck    (cio_jtag_tck),
    .jtag_tms    (cio_jtag_tms),
    .jtag_tdi    (cio_jtag_tdi),
    .jtag_tdo    (cio_jtag_tdo),
    .jtag_trst_n (cio_jtag_trst_n),
    .jtag_srst_n (cio_jtag_srst_n)
  );
`endif

  // SPI DPI
  spidpi u_spi (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .spi_device_sck_o     (cio_spi_device_sck_p2d),
    .spi_device_csb_o     (cio_spi_device_csb_p2d),
    .spi_device_mosi_o    (cio_spi_device_mosi_p2d),
    .spi_device_miso_i    (cio_spi_device_miso_d2p),
    .spi_device_miso_en_i (cio_spi_device_miso_en_d2p)
  );

  // USB DPI
  usbdpi u_usbdpi (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .clk_48MHz_i   (clk_i),
    .sense_p2d     (cio_usbdev_sense_p2d),
    .pullup_d2p    (cio_usbdev_dp_pullup_d2p),
    .pullup_en_d2p (cio_usbdev_dp_pullup_en_d2p),
    .dp_p2d        (cio_usbdev_dp_p2d),
    .dp_d2p        (cio_usbdev_dp_d2p),
    .dp_en_d2p     (cio_usbdev_dp_en_d2p),
    .dn_p2d        (cio_usbdev_dn_p2d),
    .dn_d2p        (cio_usbdev_dn_d2p),
    .dn_en_d2p     (cio_usbdev_dn_en_d2p)
  );

  // Tie off unused signals.
  logic unused_cio_usbdev_se0_d2p, unused_cio_usbdev_se0_en_d2p;
  logic unused_cio_usbdev_dn_pullup_d2p, unused_cio_usbdev_dn_pullup_en_d2p;
  logic unused_cio_usbdev_tx_mode_se_d2p, unused_cio_usbdev_tx_mode_se_en_d2p;
  logic unused_cio_usbdev_suspend_d2p, unused_cio_usbdev_suspend_en_d2p;
  logic unused_cio_usbdev_d_d2p, unused_cio_usbdev_d_en_d2p;
  assign unused_cio_usbdev_se0_d2p = cio_usbdev_se0_d2p;
  assign unused_cio_usbdev_se0_en_d2p = cio_usbdev_se0_en_d2p;
  assign unused_cio_usbdev_dn_pullup_d2p = cio_usbdev_dn_pullup_d2p;
  assign unused_cio_usbdev_dn_pullup_en_d2p = cio_usbdev_dn_pullup_en_d2p;
  assign unused_cio_usbdev_tx_mode_se_d2p = cio_usbdev_tx_mode_se_d2p;
  assign unused_cio_usbdev_tx_mode_se_en_d2p = cio_usbdev_tx_mode_se_en_d2p;
  assign unused_cio_usbdev_suspend_d2p = cio_usbdev_suspend_d2p;
  assign unused_cio_usbdev_suspend_en_d2p = cio_usbdev_suspend_en_d2p;
  assign cio_usbdev_d_p2d = 1'b0;
  assign unused_cio_usbdev_d_d2p = cio_usbdev_d_d2p;
  assign unused_cio_usbdev_d_en_d2p = cio_usbdev_d_en_d2p;

  // monitor for termination
`ifndef END_MON_PATH
  `define END_MON_PATH top_earlgrey.u_ram1p_ram_main
`endif

  logic valid;
  logic [31:0] addr;
  logic end_valid;

  // mem address in design is offset from base, re-create the full address here
  assign addr = `VERILATOR_MEM_BASE + {`END_MON_PATH.addr_i, 2'h0};
  assign valid = `END_MON_PATH.req_i & `END_MON_PATH.write_i & `END_MON_PATH.rst_ni;
  assign end_valid = valid & (addr == `VERILATOR_END_SIM_ADDR);

  always_ff @(posedge clk_i) begin
    if (end_valid) begin
      $display("Verilator sim termination requested");
      $display("Your simulation wrote to 0x%h", `VERILATOR_END_SIM_ADDR);
      $finish;
    end
  end

endmodule
