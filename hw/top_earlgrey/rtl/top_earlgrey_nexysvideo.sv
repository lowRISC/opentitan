// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_nexysvideo #(
  // Path to a VMEM file containing the contents of the boot ROM, which will be
  // baked into the FPGA bitstream.
  parameter BootRomInitFile = "boot_rom_fpga_nexysvideo.32.vmem"
) (
  // Clock and Reset
  input               IO_CLK,
  input               IO_RST_N,
  // JTAG interface
  inout               IO_DPS0, // IO_JTCK,    IO_SDCK
  inout               IO_DPS3, // IO_JTMS,    IO_SDCSB
  inout               IO_DPS1, // IO_JTDI,    IO_SDSDI
  inout               IO_DPS4, // IO_JTRST_N,
  inout               IO_DPS5, // IO_JSRST_N,
  inout               IO_DPS2, // IO_JTDO,    IO_SDO
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
  // USB interface for testing with TI1106 USB PHY
  output              IO_UPHY_DP_TX,
  output              IO_UPHY_DN_TX,
  input               IO_UPHY_DP_RX,
  input               IO_UPHY_DN_RX,
  input               IO_UPHY_D_RX,
  output              IO_UPHY_OE_N,
  input               IO_UPHY_SENSE,
  output              IO_UPHY_DPPULLUP,
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
  inout               IO_GP15,
  // GPIOs going to PMOD JA
  inout               IO_GP24,
  inout               IO_GP25,
  inout               IO_GP26,
  inout               IO_GP27,
  inout               IO_GP28,
  inout               IO_GP29,
  inout               IO_GP30,
  inout               IO_GP31
);

  import top_earlgrey_pkg::*;

  //////////////////////
  // Padring Instance //
  //////////////////////


  logic clk_main, clk_usb_48mhz, rst_n;
  logic [padctrl_reg_pkg::NMioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] mio_attr;
  logic [padctrl_reg_pkg::NDioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] dio_attr;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_out_core, mio_out_padring;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_oe_core, mio_oe_padring;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_in_core, mio_in_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_out_core, dio_out_umux, dio_out_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_oe_core, dio_oe_umux, dio_oe_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_in_core, dio_in_umux, dio_in_padring;

  padring #(
    // MIOs 23:20 are currently not
    // connected to pads and hence tied off
    .ConnectMioIn  ( 32'hFF0FFFFF ),
    .ConnectMioOut ( 32'hFF0FFFFF ),
    // Tied off DIOs:
    // 2: usbdev_d
    // 3: usbdev_suspend
    // 4: usbdev_tx_mode
    // 7: usbdev_se
    .ConnectDioIn  ( 15'h7F63 ),
    .ConnectDioOut ( 15'h7F63 )
  ) padring (
    // Clk / Rst
    .clk_pad_i           ( 1'b0 ),
    .clk_usb_48mhz_pad_i ( 1'b0 ),
    .rst_pad_ni          ( 1'b0 ),
    .clk_o               (      ),
    .clk_usb_48mhz_o     (      ),
    .rst_no              (      ),
    // MIO Pads
    .mio_pad_io          ( { IO_GP31,
                             IO_GP30,
                             IO_GP29,
                             IO_GP28,
                             IO_GP27,
                             IO_GP26,
                             IO_GP25,
                             IO_GP24,
                             4'bz,    // Note that 23:20 are currently not mapped
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
                             IO_DPS1, // SDI, JTAG_TDI
                             IO_DPS2, // SDO, JTAG_TDO
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
  logic jtag_tck, jtag_tck_buf, jtag_tms, jtag_tdi, jtag_tdo;

  localparam int NumIOs = padctrl_reg_pkg::NMioPads +
                          padctrl_reg_pkg::NDioPads;

  // This specifies the tie-off values of the muxed MIO/DIOs
  // when the JTAG is active. SPI CSB is active low.
  localparam logic [NumIOs-1:0] TieOffValues = NumIOs'(1'b1 << (
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
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSdi ),
    .TdoIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSdo )
  ) jtag_mux (
    // To JTAG inside core
    .jtag_tck_o   ( jtag_tck        ),
    .jtag_tms_o   ( jtag_tms        ),
    .jtag_trst_no ( jtag_trst_n     ),
    .jtag_srst_no ( jtag_srst_n     ),
    .jtag_tdi_o   ( jtag_tdi        ),
    .jtag_tdo_i   ( jtag_tdo        ),
    // To core side via usbmux for DIOs
    .out_core_i   ( {dio_out_umux, mio_out_core} ),
    .oe_core_i    ( {dio_oe_umux,  mio_oe_core}  ),
    .in_core_o    ( {dio_in_umux,  mio_in_core}  ),
    // To padring side
    .out_padring_o ( {dio_out_padring, mio_out_padring} ),
    .oe_padring_o  ( {dio_oe_padring, mio_oe_padring } ),
    .in_padring_i  ( {dio_in_padring, mio_in_padring } )
  );

  // Software can enable the pinflip feature inside usbdev.
  // The example hello_usbdev does this based on GPIO0 (a switch on the board)
  //
  // Here, we use the state of the DN pullup to effectively undo the
  // swapping such that the PCB always sees the unflipped D+/D-. We
  // could do the same inside the .xdc file but then two FPGA
  // bitstreams would be needed for testing.
  //
  // dio_in/out/oe map is: PADS <- _padring <- JTAG mux -> _umux -> USB mux -> _core
  localparam int DioIdxUsbDn0 = top_earlgrey_pkg::TopEarlgreyDioPinUsbdevDn;
  localparam int DioIdxUsbDp0 = top_earlgrey_pkg::TopEarlgreyDioPinUsbdevDp;
  localparam int DioIdxUsbD0  = top_earlgrey_pkg::TopEarlgreyDioPinUsbdevD;
  localparam int DioIdxUsbSense0 = top_earlgrey_pkg::TopEarlgreyDioPinUsbdevSense;
  localparam int DioIdxUsbDnPullup0 = top_earlgrey_pkg::TopEarlgreyDioPinUsbdevDnPullup;
  localparam int DioIdxUsbDpPullup0 = top_earlgrey_pkg::TopEarlgreyDioPinUsbdevDpPullup;


  // Split out for differential PHY testing

  // Outputs always drive and just copy the value
  // Let them go to the normal place too because it won't do any harm
  // and it simplifies the changes needed
  OBUF o_uphy_dp (
    .O (IO_UPHY_DP_TX),
    .I (dio_out_umux[DioIdxUsbDp0])
  );
  OBUF o_uphy_dn (
    .O (IO_UPHY_DN_TX),
    .I (dio_out_umux[DioIdxUsbDn0])
  );
  OBUF o_uphy_pu (
    .O (IO_UPHY_DPPULLUP),
    .I (dio_out_umux[DioIdxUsbDpPullup0] & dio_oe_umux[DioIdxUsbDpPullup0])
  );
  OBUF o_uphy_oe_N (
    .O (IO_UPHY_OE_N),
    .I (~dio_oe_umux[DioIdxUsbDp0])
  );

  // Input: pull to local signals and mux in loop below
  logic uphy_dp_rx, uphy_dn_rx, uphy_d_rx, uphy_sense;

  IBUF i_uphy_dp (
    .I (IO_UPHY_DP_RX),
    .O (uphy_dp_rx)
  );
  IBUF i_uphy_dn (
    .I (IO_UPHY_DN_RX),
    .O (uphy_dn_rx)
  );
  IBUF i_uphy_d (
    .I (IO_UPHY_D_RX),
    .O (uphy_d_rx)
  );
  IBUF i_uphy_sense (
    .I (IO_UPHY_SENSE),
    .O (uphy_sense)
  );


  // The output enable for IO_USB_DNPULLUP0 is used to decide whether we need to undo the swapping.
  logic undo_swap;
  assign undo_swap = dio_oe_core[DioIdxUsbDnPullup0];

  // GPIO[2] = Switch 2 on board is used to select using the UPHY
  // Keep GPIO[1] for selecting differential in sw
  logic use_uphy;
  assign use_uphy = mio_in_padring[2];

  for (genvar i = 0; i < padctrl_reg_pkg::NDioPads; i++) begin : gen_dio
    if (i == DioIdxUsbDn0) begin
      assign dio_out_umux[i] = undo_swap ? dio_out_core[DioIdxUsbDp0] :
                                           dio_out_core[DioIdxUsbDn0];
      assign dio_oe_umux[i]  = undo_swap ? dio_oe_core[DioIdxUsbDp0] :
                                           dio_oe_core[DioIdxUsbDn0];
      assign dio_in_core[i] = use_uphy ?
                              (undo_swap ? uphy_dp_rx : uphy_dn_rx) :
                              (undo_swap ? dio_in_umux[DioIdxUsbDp0] :
                                           dio_in_umux[DioIdxUsbDn0]);
    end else if (i == DioIdxUsbDp0) begin
      assign dio_out_umux[i] = undo_swap ? dio_out_core[DioIdxUsbDn0] :
                                           dio_out_core[DioIdxUsbDp0];
      assign dio_oe_umux[i]  = undo_swap ? dio_oe_core[DioIdxUsbDn0] :
                                           dio_oe_core[DioIdxUsbDp0];
      assign dio_in_core[i] = use_uphy ?
                              (undo_swap ? uphy_dn_rx : uphy_dp_rx) :
                              (undo_swap ? dio_in_umux[DioIdxUsbDn0] :
                                           dio_in_umux[DioIdxUsbDp0]);
    end else if (i == DioIdxUsbD0) begin
      assign dio_out_umux[i] = undo_swap ? ~dio_out_core[DioIdxUsbD0] :
                                            dio_out_core[DioIdxUsbD0];
      assign dio_oe_umux[i]  = dio_oe_core[i];
      assign dio_in_core[i] = use_uphy ?
                              (undo_swap ? ~uphy_d_rx : uphy_d_rx) :
                              (undo_swap ? ~dio_in_umux[DioIdxUsbD0] :
                                            dio_in_umux[DioIdxUsbD0]);
    end else if (i == DioIdxUsbDnPullup0) begin
      assign dio_out_umux[i] = undo_swap ? dio_out_core[DioIdxUsbDpPullup0] :
                                           dio_out_core[DioIdxUsbDnPullup0];
      assign dio_oe_umux[i]  = undo_swap ? dio_oe_core[DioIdxUsbDpPullup0] :
                                           dio_oe_core[DioIdxUsbDnPullup0];
      assign dio_in_core[i]  = dio_in_umux[i];
    end else if (i == DioIdxUsbDpPullup0) begin
      assign dio_out_umux[i] = undo_swap ? dio_out_core[DioIdxUsbDnPullup0] :
                                           dio_out_core[DioIdxUsbDpPullup0];
      assign dio_oe_umux[i]  = undo_swap ? dio_oe_core[DioIdxUsbDnPullup0] :
                                           dio_oe_core[DioIdxUsbDpPullup0];
      assign dio_in_core[i]  = dio_in_umux[i];
    end else if (i == DioIdxUsbSense0) begin
      assign dio_out_umux[i] = dio_out_core[i];
      assign dio_oe_umux[i]  = dio_oe_core[i];
      assign dio_in_core[i]  = use_uphy ? uphy_sense : dio_in_umux[i];
    end else begin
      assign dio_out_umux[i] = dio_out_core[i];
      assign dio_oe_umux[i]  = dio_oe_core[i];
      assign dio_in_core[i]  = dio_in_umux[i];
    end
  end

  ////////////////////////////////
  // JTAG clock buffer for FPGA //
  ////////////////////////////////

  BUFG jtag_buf (
    .I (jtag_tck),
    .O (jtag_tck_buf)
  );

  //////////////////
  // PLL for FPGA //
  //////////////////

  clkgen_xil7series # (
    .AddClkBuf(0)
  ) clkgen (
    .IO_CLK,
    .IO_RST_N,
    .jtag_srst_n,
    .clk_main(clk_main),
    .clk_48MHz(clk_usb_48mhz),
    .rst_n(rst_n)
  );

  //////////////////////
  // Top-level design //
  //////////////////////
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  ast_wrapper_pkg::ast_rst_t ast_base_rst;
  ast_wrapper_pkg::ast_alert_req_t ast_base_alerts;
  ast_wrapper_pkg::ast_status_t ast_base_status;

  assign ast_base_pwr.slow_clk_val = pwrmgr_pkg::DiffValid;
  assign ast_base_pwr.core_clk_val = pwrmgr_pkg::DiffValid;
  assign ast_base_pwr.io_clk_val   = pwrmgr_pkg::DiffValid;
  assign ast_base_pwr.usb_clk_val  = pwrmgr_pkg::DiffValid;
  assign ast_base_pwr.main_pok     = 1'b1;

  assign ast_base_alerts.alerts_p  = '0;
  assign ast_base_alerts.alerts_n  = {ast_wrapper_pkg::NumAlerts{1'b1}};
  assign ast_base_status.io_pok    = {ast_wrapper_pkg::NumIoRails{1'b1}};

  // the rst_ni pin only goes to AST
  // the rest of the logic generates reset based on the 'pok' signal.
  // for verilator purposes, make these two the same.
  assign ast_base_rst.aon_pok      = rst_n;
  top_earlgrey #(
    .AesMasking(1'b0),
    .AesSBoxImpl(aes_pkg::SBoxImplLut),
    .SecAesStartTriggerDelay(0),
    .SecAesAllowForcingMasks(1'b0),
    .IbexRegFile(ibex_pkg::RegFileFPGA),
    .IbexPipeLine(1),
    .OtbnRegFile(otbn_pkg::RegFileFPGA),
    .BootRomInitFile(BootRomInitFile)
  ) top_earlgrey (
    // Clocks, resets
    .rst_ni          ( rst_n         ),
    .clk_main_i      ( clk_main      ),
    .clk_io_i        ( clk_main      ),
    .clk_usb_i       ( clk_usb_48mhz ),
    .clk_aon_i       ( clk_main      ),
    .rstmgr_ast_i                 ( ast_base_rst    ),
    .pwrmgr_pwr_ast_req_o         (                 ),
    .pwrmgr_pwr_ast_rsp_i         ( ast_base_pwr    ),
    .sensor_ctrl_ast_alert_req_i  ( ast_base_alerts ),
    .sensor_ctrl_ast_alert_rsp_o  (                 ),
    .sensor_ctrl_ast_status_i     ( ast_base_status ),
    .usbdev_usb_ref_val_o         (                 ),
    .usbdev_usb_ref_pulse_o       (                 ),
    .ast_tl_req_o                 (                 ),
    .ast_tl_rsp_i                 ( '0              ),
    .otp_ctrl_otp_ast_pwr_seq_o   (                 ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( '0              ),
    .flash_power_down_h_i         ( '0              ),
    .flash_power_ready_h_i        ( 1'b1            ),

    // JTAG
    .jtag_tck_i      ( jtag_tck_buf  ),
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

    // DFT signals
    .scan_rst_ni     ( 1'b1          ),
    .scanmode_i      ( 1'b0          )
  );

endmodule : top_earlgrey_nexysvideo
