// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_asic (
  // Clock and Reset
  inout               IO_CLK,
  inout               IO_RST_N,
  inout               IO_CLK_USB_48MHZ,
  // JTAG interface
  inout               IO_DPS0, // IO_JTCK,    IO_SDCK
  inout               IO_DPS3, // IO_JTMS,    IO_SDCSB
  inout               IO_DPS1, // IO_JTDI,    IO_SDMOSI
  inout               IO_DPS4, // IO_JTRST_N,
  inout               IO_DPS5, // IO_JSRST_N,
  inout               IO_DPS2, // IO_JTDO,    IO_MISO
  inout               IO_DPS6, // JTAG=1,     SPI=0
  inout               IO_DPS7, // BOOTSTRAP=1
  // UART interface
  inout               IO_URX,
  inout               IO_UTX,
  // USB interface
  inout               IO_USB_DP0,
  inout               IO_USB_DN0,
  inout               IO_USB_SENSE0,
  inout               IO_USB_DNPULLUP0,
  inout               IO_USB_DPPULLUP0,
  // GPIO x 16 interface
  inout               IO_GP0,
  inout               IO_GP1,
  inout               IO_GP2,
  inout               IO_GP3,
  inout               IO_GP4,
  inout               IO_GP5,
  inout               IO_GP6,
  inout               IO_GP7,
  inout               IO_GP8,
  inout               IO_GP9,
  inout               IO_GP10,
  inout               IO_GP11,
  inout               IO_GP12,
  inout               IO_GP13,
  inout               IO_GP14,
  inout               IO_GP15
);

  import top_earlgrey_pkg::*;

  ////////////////////////
  // Signal definitions //
  ////////////////////////

  //////////////////////
  // Padring Instance //
  //////////////////////

  logic clk, clk_usb_48mhz, rst_n;
  logic [padctrl_reg_pkg::NMioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] mio_attr;
  logic [padctrl_reg_pkg::NDioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] dio_attr;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_out_core, mio_out_padring;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_oe_core, mio_oe_padring;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_in_core, mio_in_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_out_core, dio_out_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_oe_core, dio_oe_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_in_core, dio_in_padring;

  padring #(
    // MIOs 31:20 are currently not
    // connected to pads and hence tied off
    .ConnectMioIn  ( 32'h000FFFFF ),
    .ConnectMioOut ( 32'h000FFFFF ),
    // Tied off DIOs:
    // 2: usbdev_d
    // 3: usbdev_suspend
    // 4: usbdev_tx_mode
    // 7: usbdev_se
    .ConnectDioIn  ( 15'h7F63 ),
    .ConnectDioOut ( 15'h7F63 )
  ) padring (
    // Clk / Rst
    .clk_pad_i           ( IO_CLK           ),
    .clk_usb_48mhz_pad_i ( IO_CLK_USB_48MHZ ),
    .rst_pad_ni          ( IO_RST_N         ),
    .clk_o               ( clk              ),
    .clk_usb_48mhz_o     ( clk_usb_48mhz    ),
    .rst_no              ( rst_n            ),
    // MIO Pads
    .mio_pad_io          ( { 12'bz,   // Note that 31:20 are currently not mapped
                             IO_DPS5, // Use GPIO19 to pass JTAG_SRST
                             IO_DPS4, // Use GPIO18 to pass JTAG_TRST
                             IO_DPS7, // Use GPIO17 to pass rom boot_strap indication
                             IO_DPS6, // Use GPIO16 to pass SPI/JTAG control flag
                             IO_GP15,
                             IO_GP14,
                             IO_GP13,
                             IO_GP12,
                             IO_GP11,
                             IO_GP10,
                             IO_GP9,
                             IO_GP8,
                             IO_GP7,
                             IO_GP6,
                             IO_GP5,
                             IO_GP4,
                             IO_GP3,
                             IO_GP2,
                             IO_GP1,
                             IO_GP0 } ),
    // DIO Pads
    .dio_pad_io          ( { IO_DPS0, // SCK, JTAG_TCK
                             IO_DPS3, // CSB, JTAG_TMS
                             IO_DPS1, // MOSI, JTAG_TDI
                             IO_DPS2, // MISO, JTAG_TDO
                             IO_URX,
                             IO_UTX,
                             IO_USB_SENSE0,
                             1'bz,    // usbdev_se0
                             IO_USB_DPPULLUP0,
                             IO_USB_DNPULLUP0,
                             1'bz,    // usbdev_tx_mode
                             1'bz,    // usbdev_suspend
                             1'bz,    // usbdev_d
                             IO_USB_DP0,
                             IO_USB_DN0 } ),
    // Muxed IOs
    .mio_in_o            ( mio_in_padring   ),
    .mio_out_i           ( mio_out_padring  ),
    .mio_oe_i            ( mio_oe_padring   ),
    // Dedicated IOs
    .dio_in_o            ( dio_in_padring   ),
    .dio_out_i           ( dio_out_padring  ),
    .dio_oe_i            ( dio_oe_padring   ),
    // Pad Attributes
    .mio_attr_i          ( mio_attr         ),
    .dio_attr_i          ( dio_attr         )
  );

  //////////////////////
  // JTAG Overlay Mux //
  //////////////////////

  logic jtag_trst_n, jtag_srst_n;
  logic jtag_tck, jtag_tms, jtag_tdi, jtag_tdo;

  localparam int NumIOs = padctrl_reg_pkg::NMioPads +
                          padctrl_reg_pkg::NDioPads;

  // This specifies the tie-off values of the muxed MIO/DIOs
  // when the JTAG is active. SPI CSB is active low.
  localparam logic [NumIOs-1:0] TieOffValues =NumIOs'(1'b1 << (
      padctrl_reg_pkg::NMioPads + top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceCsb));

  // TODO: this is a temporary solution. JTAG will eventually be selected and
  // qualified inside the pinmux, based on strap and lifecycle state.
  // Parameterizeable JTAG overlay mux.
  // Unaffected indices are just passed through.
  jtag_mux #(
    .NumIOs         (                   NumIOs       ),
    .TieOffValues   (                   TieOffValues ),
    .JtagEnIdx      (                             16 ), // MIO 16
    .JtagEnPolarity (                              1 ),
    .TckIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSck ),
    .TmsIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceCsb ),
    .TrstIdx        (                             18 ), // MIO 18
    .SrstIdx        (                             19 ), // MIO 19
    .TdiIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceMosi ),
    .TdoIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceMiso )
  ) jtag_mux (
    // To JTAG inside core
    .jtag_tck_o   ( jtag_tck        ),
    .jtag_tms_o   ( jtag_tms        ),
    .jtag_trst_no ( jtag_trst_n     ),
    .jtag_srst_no ( jtag_srst_n     ),
    .jtag_tdi_o   ( jtag_tdi        ),
    .jtag_tdo_i   ( jtag_tdo        ),
    // To core side
    .out_core_i   ( {dio_out_core, mio_out_core} ),
    .oe_core_i    ( {dio_oe_core,  mio_oe_core}  ),
    .in_core_o    ( {dio_in_core,  mio_in_core}  ),
    // To padring side
    .out_padring_o ( {dio_out_padring, mio_out_padring} ),
    .oe_padring_o  ( {dio_oe_padring , mio_oe_padring } ),
    .in_padring_i  ( {dio_in_padring , mio_in_padring } )
  );

  //////////////////////
  // AST              //
  //////////////////////
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;
  ast_wrapper_pkg::ast_status_t ast_base_status;
  ast_wrapper_pkg::ast_alert_req_t ast_base_alerts;
  ast_wrapper_pkg::ast_alert_rsp_t base_ast_alerts;
  ast_wrapper_pkg::ast_rst_t ast_base_rst;
  ast_wrapper_pkg::ast_clks_t ast_base_clks;
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  sensor_ctrl_pkg::ast_aux_t base_ast_aux;
  entropy_src_pkg::entropy_src_rng_req_t base_ast_entropy_src;
  entropy_src_pkg::entropy_src_rng_rsp_t ast_base_entropy_src;

  // TODO: Connect to AST Wrapper
  assign entropy_src_rng_rsp = '0;

  logic usb_ref_pulse;
  logic usb_ref_val;


  ast_wrapper ast_wrapper (
    .clk_ext_i(clk),
    .por_ni(rst_n),
    .bus_i(base_ast_bus),
    .bus_o(ast_base_bus),
    .pwr_i(base_ast_pwr),
    .pwr_o(ast_base_pwr),
    .rst_o(ast_base_rst),
    .clks_o(ast_base_clks),
    .usb_ref_pulse_i(usb_ref_pulse),
    .usb_ref_val_i(usb_ref_val),
    .aux_i(base_ast_aux),
    .adc_i('0),
    .adc_o(),
    .es_i(base_ast_entropy_src),
    .es_o(ast_base_entropy_src),
    .alert_i(base_ast_alerts),
    .alert_o(ast_base_alerts),
    .status_o(ast_base_status)
  );


  //////////////////////
  // Top-level design //
  //////////////////////

  top_earlgrey top_earlgrey (
    .rst_ni              ( rst_n                 ),
    .clkmgr_aon_clk_main ( ast_base_clks.clk_sys ),
    .clkmgr_aon_clk_io   ( ast_base_clks.clk_io  ),
    .clkmgr_aon_clk_usb  ( ast_base_clks.clk_usb ),
    .clkmgr_aon_clk_aon  ( ast_base_clks.clk_aon ),

    // JTAG
    .jtag_tck_i      ( jtag_tck      ),
    .jtag_tms_i      ( jtag_tms      ),
    .jtag_trst_ni    ( jtag_trst_n   ),
    .jtag_tdi_i      ( jtag_tdi      ),
    .jtag_tdo_o      ( jtag_tdo      ),

    // Multiplexed I/O
    .mio_in_i        ( mio_in_core   ),
    .mio_out_o       ( mio_out_core  ),
    .mio_oe_o        ( mio_oe_core   ),

    // Dedicated I/O
    .dio_in_i        ( dio_in_core   ),
    .dio_out_o       ( dio_out_core  ),
    .dio_oe_o        ( dio_oe_core   ),

    // Pad attributes
    .mio_attr_o      ( mio_attr      ),
    .dio_attr_o      ( dio_attr      ),

    // AST connections
    .sensor_ctrl_ast_host            ( base_ast_bus         ),
    .sensor_ctrl_ast_dev             ( ast_base_bus         ),
    .sensor_ctrl_ast_status          ( ast_base_status      ),
    .sensor_ctrl_ast_alert_req       ( ast_base_alerts      ),
    .sensor_ctrl_ast_alert_rsp       ( base_ast_alerts      ),
    .pwrmgr_aon_pwr_ast_req          ( base_ast_pwr         ),
    .pwrmgr_aon_pwr_ast_rsp          ( ast_base_pwr         ),
    .rstmgr_aon_ast                  ( ast_base_rst         ),
    .usbdev_aon_usb_ref_pulse        ( usb_ref_pulse        ),
    .usbdev_aon_usb_ref_val          ( usb_ref_val          ),
    .sensor_ctrl_ast_aux             ( base_ast_aux         ),
    .entropy_src_entropy_src_rng_req ( base_ast_entropy_src ),
    .entropy_src_entropy_src_rng_rsp ( ast_base_entropy_src ),

    // DFT signals
    .scan_rst_ni     ( 1'b1          ),
    .scanmode_i      ( 1'b0          )
  );

endmodule : top_earlgrey_asic
