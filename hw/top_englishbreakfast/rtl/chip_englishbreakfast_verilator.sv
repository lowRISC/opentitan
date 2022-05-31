// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module chip_englishbreakfast_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni
);

  import top_englishbreakfast_pkg::*;

  logic [31:0]  cio_gpio_p2d, cio_gpio_d2p, cio_gpio_en_d2p;
  logic cio_uart_rx_p2d, cio_uart_tx_d2p, cio_uart_tx_en_d2p;

  logic cio_spi_device_sck_p2d, cio_spi_device_csb_p2d;
  logic cio_spi_device_sdi_p2d;
  logic cio_spi_device_sdo_d2p, cio_spi_device_sdo_en_d2p;

  logic cio_usbdev_sense_p2d;
  logic cio_usbdev_se0_d2p;
  logic cio_usbdev_dp_pullup_d2p;
  logic cio_usbdev_dn_pullup_d2p;
  logic cio_usbdev_rx_enable_d2p;
  logic cio_usbdev_tx_use_d_se0_d2p;
  logic cio_usbdev_d_p2d, cio_usbdev_d_d2p, cio_usbdev_d_en_d2p;
  logic cio_usbdev_dp_p2d, cio_usbdev_dp_d2p, cio_usbdev_dp_en_d2p;
  logic cio_usbdev_dn_p2d, cio_usbdev_dn_d2p, cio_usbdev_dn_en_d2p;

  logic IO_JTCK, IO_JTMS, IO_JTRST_N, IO_JTDI, IO_JTDO;

  // TODO: instantiate padring and route these signals through that module
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;

  always_comb begin : assign_dio_in
    dio_in = '0;
    dio_in[DioSpiDeviceSck] = cio_spi_device_sck_p2d;
    dio_in[DioSpiDeviceCsb] = cio_spi_device_csb_p2d;
    dio_in[DioSpiDeviceSd0] = cio_spi_device_sdi_p2d;
    dio_in[DioUsbdevUsbDp] = cio_usbdev_dp_p2d;
    dio_in[DioUsbdevUsbDn] = cio_usbdev_dn_p2d;
  end

  logic usb_dp_pullup;
  logic usb_dn_pullup;
  logic usb_rx_d;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_use_d_se0;
  logic usb_rx_enable;

  assign usb_rx_d = cio_usbdev_d_p2d;
  assign cio_usbdev_dn_d2p = dio_out[DioUsbdevUsbDn];
  assign cio_usbdev_dp_d2p = dio_out[DioUsbdevUsbDp];
  assign cio_usbdev_d_d2p  = usb_tx_d;
  assign cio_usbdev_rx_enable_d2p = usb_rx_enable;
  assign cio_usbdev_tx_use_d_se0_d2p = usb_tx_use_d_se0;
  assign cio_usbdev_dn_pullup_d2p = usb_dn_pullup;
  assign cio_usbdev_dp_pullup_d2p = usb_dp_pullup;
  assign cio_usbdev_se0_d2p = usb_tx_se0;
  assign cio_spi_device_sdo_d2p = dio_out[DioSpiDeviceSd1];

  assign cio_usbdev_dn_en_d2p = dio_oe[DioUsbdevUsbDn];
  assign cio_usbdev_dp_en_d2p = dio_oe[DioUsbdevUsbDp];
  assign cio_usbdev_d_en_d2p  = dio_oe[DioUsbdevUsbDp];
  assign cio_spi_device_sdo_en_d2p = dio_oe[DioSpiDeviceSd1];

  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe;

  always_comb begin : assign_mio_in
    mio_in = '0;
    mio_in[31:0] = cio_gpio_p2d;
    mio_in[25] = cio_uart_rx_p2d;
    mio_in[35] = cio_usbdev_sense_p2d;
    mio_in[36] = cio_usbdev_sense_p2d;
  end

  assign cio_gpio_d2p[25:0]       = mio_out[25:0];
  assign cio_gpio_en_d2p[25:0]    = mio_oe[25:0];
  assign cio_gpio_d2p[31:27]      = mio_out[31:27];
  assign cio_gpio_en_d2p[31:27]   = mio_oe[31:27];
  assign cio_uart_tx_d2p    = mio_out[26];
  assign cio_uart_tx_en_d2p = mio_oe[26];

  // dummy ast connections
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  ast_pkg::ast_alert_req_t ast_base_alerts;
  ast_pkg::ast_status_t ast_base_status;

  assign ast_base_pwr.slow_clk_val = 1'b1;
  assign ast_base_pwr.core_clk_val = 1'b1;
  assign ast_base_pwr.io_clk_val   = 1'b1;
  assign ast_base_pwr.usb_clk_val  = 1'b1;
  assign ast_base_pwr.main_pok     = 1'b1;

  ast_pkg::ast_dif_t silent_alert = '{
                                       p: 1'b0,
                                       n: 1'b1
                                     };

  assign ast_base_alerts.alerts = {ast_pkg::NumAlerts{silent_alert}};
  assign ast_base_status.io_pok = {ast_pkg::NumIoRails{1'b1}};

  // the rst_ni pin only goes to AST
  // the rest of the logic generates reset based on the 'pok' signal.
  // for verilator purposes, make these two the same.

  logic clk_aon;
  // reset is not used below becuase verilator uses only sync resets
  // and also does not under 'x'.
  // if we allow the divider below to reset, clk_aon will be silenced,
  // and as a result all the clk_aon logic inside top_englishbreakfast does not
  // get reset
  prim_clock_div #(
    .Divisor(4)
  ) u_aon_div (
    .clk_i,
    .rst_ni(1'b1),
    .step_down_req_i('0),
    .step_down_ack_o(),
    .test_en_i('0),
    .clk_o(clk_aon)
  );

  // TODO: generate these indices from the target-specific
  // pinout configuration. But first, this verilator top needs
  // to be split into a Verilator TB and a Verilator chiplevel.
  // DFT and Debug signal positions in the pinout.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    tck_idx:        pinmux_reg_pkg::NMioPads +
                    top_englishbreakfast_pkg::DioSpiDeviceSck,
    tms_idx:        pinmux_reg_pkg::NMioPads +
                    top_englishbreakfast_pkg::DioSpiDeviceCsb,
    trst_idx:       18, // MIO 18
    tdi_idx:        pinmux_reg_pkg::NMioPads +
                    top_englishbreakfast_pkg::DioSpiDeviceSd0,
    tdo_idx:        pinmux_reg_pkg::NMioPads +
                    top_englishbreakfast_pkg::DioSpiDeviceSd1,
    tap_strap0_idx: 26, // MIO 26
    tap_strap1_idx: 16, // MIO 16 (this is different in the ASIC top)
    dft_strap0_idx: 21, // MIO 21
    dft_strap1_idx: 22, // MIO 22
    // TODO: check whether there is a better way to pass these USB-specific params
    usb_dp_idx:        DioUsbdevUsbDp,
    usb_dn_idx:        DioUsbdevUsbDn,
    usb_sense_idx:     MioInUsbdevSense,
    // TODO: connect these once the verilator chip-level has been merged with the chiplevel.sv.tpl
    dio_pad_type: {pinmux_reg_pkg::NDioPads{prim_pad_wrapper_pkg::BidirStd}},
    mio_pad_type: {pinmux_reg_pkg::NMioPads{prim_pad_wrapper_pkg::BidirStd}}
  };


  prim_mubi_pkg::mubi4_t all_clk_bypass;
  prim_mubi_pkg::mubi4_t io_clk_bypass;
  // Top-level design
  top_englishbreakfast #(
    .SecAesMasking(1'b1),
    .SecAesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(40),
    .SecAesAllowForcingMasks(1'b1),
    .SecAesSkipPRNGReseeding(1'b1),
    .RvCoreIbexICache(0),
    .SramCtrlRetAonInstrExec(0),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_englishbreakfast (
    .por_n_i                      ({rst_ni, rst_ni}  ),
    .clk_main_i                   (clk_i             ),
    .clk_io_i                     (clk_i             ),
    .clk_usb_i                    (clk_i             ),
    .clk_aon_i                    (clk_aon           ),
    .clk_main_jitter_en_o         (                  ),
    .pwrmgr_ast_req_o             (                  ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr     ),
    .usbdev_usb_ref_val_o         (                  ),
    .usbdev_usb_ref_pulse_o       (                  ),
    .ast_edn_req_i                ( '0               ),
    .ast_edn_rsp_o                (                  ),
    .flash_bist_enable_i          ( lc_ctrl_pkg::Off ),
    .flash_power_down_h_i         ( 1'b0             ),
    .flash_power_ready_h_i        ( 1'b1             ),
    .all_clk_byp_req_o            ( all_clk_bypass    ),
    .all_clk_byp_ack_i            ( all_clk_bypass    ),
    .io_clk_byp_req_o             ( io_clk_bypass    ),
    .io_clk_byp_ack_i             ( io_clk_bypass    ),

    // USB signals
    .usb_dp_pullup_en_o           (usb_dp_pullup),
    .usb_dn_pullup_en_o           (usb_dn_pullup),
    .usbdev_usb_rx_d_i            (usb_rx_d),
    .usbdev_usb_tx_d_o            (usb_tx_d),
    .usbdev_usb_tx_se0_o          (usb_tx_se0),
    .usbdev_usb_tx_use_d_se0_o      (usb_tx_use_d_se0),
    .usbdev_usb_rx_enable_o       (usb_rx_enable),

    // Multiplexed I/O
    .mio_in_i                     (mio_in),
    .mio_out_o                    (mio_out),
    .mio_oe_o                     (mio_oe),

    // Dedicated I/O
    .dio_in_i                     (dio_in),
    .dio_out_o                    (dio_out),
    .dio_oe_o                     (dio_oe),

    // Pad attributes
    .mio_attr_o                   ( ),
    .dio_attr_o                   ( ),

    // Memory attributes
    .ram_1p_cfg_i                 ('0),
    .ram_2p_cfg_i                 ('0),
    .rom_cfg_i                    ('0),

    // DFT signals
    .scan_rst_ni                  (1'b1),
    .scan_en_i                    (1'b0),
    .scanmode_i                   (lc_ctrl_pkg::Off)
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
  // The baud rate set to match FPGA implementation; the frequency is "artificial". Both baud rate
  // frequency must match the settings used in the on-chip software at
  // `sw/device/lib/arch/device_sim_verilator.c`.
  uartdpi #(
    .BAUD('d7_200),
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
  // TODO: this is currently not supported.
  // connect this to the correct pins once pinout is final and once the
  // verilator testbench supports DFT/Debug strap sampling.
  // See also #5221.
  //
  // jtagdpi u_jtagdpi (
  //   .clk_i,
  //   .rst_ni,

  //   .jtag_tck    (cio_jtag_tck),
  //   .jtag_tms    (cio_jtag_tms),
  //   .jtag_tdi    (cio_jtag_tdi),
  //   .jtag_tdo    (cio_jtag_tdo),
  //   .jtag_trst_n (cio_jtag_trst_n),
  //   .jtag_srst_n (cio_jtag_srst_n)
  // );
`endif

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

  // USB DPI
  usbdpi u_usbdpi (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .clk_48MHz_i     (clk_i),
    .sense_p2d       (cio_usbdev_sense_p2d),
    .pullupdp_d2p    (cio_usbdev_dp_pullup_d2p),
    .pullupdn_d2p    (cio_usbdev_dn_pullup_d2p),
    .dp_p2d          (cio_usbdev_dp_p2d),
    .dp_d2p          (cio_usbdev_dp_d2p),
    .dp_en_d2p       (cio_usbdev_dp_en_d2p),
    .dn_p2d          (cio_usbdev_dn_p2d),
    .dn_d2p          (cio_usbdev_dn_d2p),
    .dn_en_d2p       (cio_usbdev_dn_en_d2p),
    .d_p2d           (cio_usbdev_d_p2d),
    .d_d2p           (cio_usbdev_d_d2p),
    .d_en_d2p        (cio_usbdev_d_en_d2p),
    .se0_d2p         (cio_usbdev_se0_d2p),
    .rx_enable_d2p   (cio_usbdev_rx_enable_d2p),
    .tx_use_d_se0_d2p(cio_usbdev_tx_use_d_se0_d2p)
  );

  `define RV_CORE_IBEX      top_englishbreakfast.u_rv_core_ibex
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

endmodule : chip_englishbreakfast_verilator
