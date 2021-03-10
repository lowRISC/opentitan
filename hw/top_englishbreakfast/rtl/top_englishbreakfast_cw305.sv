// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_englishbreakfast_cw305 #(
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
  // ChipWhisperer IO
  output              TIO_CLKOUT,
  output              IO_UTX_DEBUG
);

  import top_englishbreakfast_pkg::*;

  //////////////////////
  // Padring Instance //
  //////////////////////


  logic clk_main, clk_usb_48mhz, clk_aon, rst_n;
  logic [pinmux_reg_pkg::NMioPads-1:0][pinmux_reg_pkg::AttrDw-1:0] mio_attr;
  logic [pinmux_reg_pkg::NDioPads-1:0][pinmux_reg_pkg::AttrDw-1:0] dio_attr;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out_core;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe_core;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_core;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out_core, dio_out_umux;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe_core, dio_oe_umux;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in_core, dio_in_umux;

  padring #(
    // MIOs 43:34 and 31:20 are currently not
    // connected to pads and hence tied off
    .ConnectMioIn  ( 44'h003_000F_FFFF ),
    .ConnectMioOut ( 44'h003_000F_FFFF ),
    // Tied off DIOs:
    // 2: usbdev_d
    // 3: usbdev_suspend
    // 4: usbdev_tx_mode
    // 7: usbdev_se
    // 9-14: spi_host all signals
    // 17-18: spi_device unused quad signals
    .ConnectDioIn  ( 21'h19_8163 ),
    .ConnectDioOut ( 21'h19_8163 ),
    // MIO pad types
    .MioPadVariant ( { // RBox
                       2'd3, // IOR13   -- open drain
                       2'd3, // IOR12   -- open drain
                       2'd3, // IOR11   -- open drain
                       2'd3, // IOR10   -- open drain
                       2'd3, // IOR9    -- open drain
                       2'd3, // IOR8    -- open drain
                       2'd0, // IOR7    -- bidir
                       2'd0, // IOR6    -- bidir
                       2'd0, // IOR5    -- bidir
                       2'd0, // IOR4    -- bidir
                       2'd0, // IOR3    -- bidir
                       2'd0, // IOR2    -- bidir
                       2'd0, // IOR1    -- bidir
                       2'd0, // IOR0    -- bidir
                       // Bank C
                       2'd3, // IOC11   -- open drain
                       2'd3, // IOC10   -- open drain
                       2'd3, // IOC9    -- open drain
                       2'd3, // IOC8    -- open drain
                       2'd0, // IOC7    -- bidir
                       2'd0, // IOC6    -- bidir
                       2'd0, // IOC5    -- bidir
                       2'd0, // IOC4    -- bidir
                       2'd0, // IOC3    -- bidir
                       2'd0, // IOC2    -- bidir
                       2'd0, // IOC1    -- bidir
                       2'd0, // IOC0    -- bidir
                       // Bank B
                       2'd3, // IOB11   -- open drain
                       2'd3, // IOB10   -- open drain
                       2'd3, // IOB9    -- open drain
                       2'd3, // IOB8    -- open drain
                       2'd0, // IOB7    -- birid
                       2'd0, // IOB6    -- birid
                       2'd0, // IOB5    -- birid
                       2'd0, // IOB4    -- birid
                       2'd0, // IOB3    -- bidir
                       2'd0, // IOB2    -- bidir
                       2'd0, // IOB1    -- bidir
                       2'd0, // IOB0    -- bidir
                       // Bank A
                       2'd3, // IOA5    -- open drain
                       2'd3, // IOA4    -- open drain
                       2'd0, // IOA3    -- bidir
                       2'd0, // IOA2    -- bidir
                       2'd0, // IOA1    -- bidir
                       2'd0  // IOA0    -- bidir
                      } ),
    // DIO pad types
    .DioPadVariant (  { 2'd1, // SPI_DEV_CLK    -- input only
                        2'd1, // SPI_DEV_CS_L   -- input only
                        2'd0, // SPI_DEV_D3     -- bidir
                        2'd0, // SPI_DEV_D2     -- bidir
                        2'd0, // SPI_DEV_D1     -- bidir
                        2'd0, // SPI_DEV_D0     -- bidir
                        2'd0, // SPI_HOST_CLK   -- bidir
                        2'd0, // SPI_HOST_CS_L  -- bidir
                        2'd0, // SPI_HOST_D3    -- bidir
                        2'd0, // SPI_HOST_D2    -- bidir
                        2'd0, // SPI_HOST_D1    -- bidir
                        2'd0, // SPI_HOST_D0    -- bidir
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd2, // USB_P          -- tolerant
                        2'd2  // USB_N          -- tolerant
                      } )
  ) padring (
    // Clk / Rst
    .clk_pad_i           ( 1'b0 ),
    .rst_pad_ni          ( 1'b0 ),
    .clk_o               (      ),
    .rst_no              (      ),
    .cc1_i               ( 1'b0 ),
    .cc2_i               ( 1'b0 ),
    // MIO Pads
    .mio_pad_io          ( { 10'bz,    // Note that 43:34 are currently not mapped
                             IO_UTX,
                             IO_URX,
                             12'bz,    // Note that 31:20 are currently not mapped
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
                             2'bz,    // quad SPI device signals are not mapped
                             IO_DPS2, // SDO, JTAG_TDO
                             IO_DPS1, // SDI, JTAG_TDI
                             6'bz,    // SPI host signals are not mapped
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
    .mio_in_o            ( mio_in_core   ),
    .mio_out_i           ( mio_out_core  ),
    .mio_oe_i            ( mio_oe_core   ),
    // Dedicated IOs
    .dio_in_o            ( dio_in_umux   ),
    .dio_out_i           ( dio_out_umux  ),
    .dio_oe_i            ( dio_oe_umux   ),
    // Pad Attributes
    .mio_attr_i          ( mio_attr      ),
    .dio_attr_i          ( dio_attr      )
  );

  //////////////////
  // PLL for FPGA //
  //////////////////

  // TODO: This needs to become a dedicated custom pin for FPGAs
  logic jtag_srst_n;
  assign jtag_srst_n = mio_in_core[19];

  clkgen_xil7series # (
    .AddClkBuf(0)
  ) clkgen (
    .IO_CLK,
    .IO_RST_N,
    .jtag_srst_n,
    .clk_main(clk_main),
    .clk_48MHz(clk_usb_48mhz),
    .clk_aon(clk_aon),
    .rst_n(rst_n)
  );

  //////////////////////
  // Top-level design //
  //////////////////////
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
  lc_ctrl_pkg::lc_tx_t lc_clk_bypass;

  // TODO: this is temporary and will be removed in the future.
  // This specifies the tie-off values of the muxed MIO/DIOs
  // when the JTAG is active. SPI CSB is active low.
  localparam logic [pinmux_pkg::NumIOs-1:0] TieOffValues = pinmux_pkg::NumIOs'(1'b1 << (
      pinmux_reg_pkg::NMioPads + top_englishbreakfast_pkg::TopEnglishbreakfastDioPinSpiDeviceCsb));

  // DFT and Debug signal positions in the pinout.
  // TODO: generate these indices from the target-specific
  // pinout configuration.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    const_sampling: 1'b1,
    tie_offs:       TieOffValues,
    tck_idx:        pinmux_reg_pkg::NMioPads +
                    top_englishbreakfast_pkg::TopEnglishbreakfastDioPinSpiDeviceSck,
    tms_idx:        pinmux_reg_pkg::NMioPads +
                    top_englishbreakfast_pkg::TopEnglishbreakfastDioPinSpiDeviceCsb,
    trst_idx:       18, // MIO 18
    tdi_idx:        pinmux_reg_pkg::NMioPads +
                    top_englishbreakfast_pkg::TopEnglishbreakfastDioPinSpiDeviceSd0,
    tdo_idx:        pinmux_reg_pkg::NMioPads +
                    top_englishbreakfast_pkg::TopEnglishbreakfastDioPinSpiDeviceSd1,
    tap_strap0_idx: 20, // MIO 20 (tied off)
    tap_strap1_idx: 16, // MIO 16 (used as JTAG/SPI select signal)
    dft_strap0_idx: 21, // MIO 21 (tied off)
    dft_strap1_idx: 22  // MIO 22 (tied off)
  };

  top_englishbreakfast #(
    .AesMasking(1'b1),
    .AesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(40),
    .SecAesAllowForcingMasks(1'b1),
    .SecAesSkipPRNGReseeding(1'b1),
    .IbexRegFile(ibex_pkg::RegFileFPGA),
    .IbexICache(0),
    .IbexPipeLine(1),
    .BootRomInitFile(BootRomInitFile),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_englishbreakfast (
    // Clocks, resets
    .rst_ni                       ( rst_n           ),
    .clk_main_i                   ( clk_main        ),
    .clk_io_i                     ( clk_main        ),
    .clk_usb_i                    ( clk_usb_48mhz   ),
    .clk_aon_i                    ( clk_aon         ),
    .pwrmgr_ast_req_o             (                 ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr    ),
    .sensor_ctrl_ast_alert_req_i  ( ast_base_alerts ),
    .sensor_ctrl_ast_alert_rsp_o  (                 ),
    .sensor_ctrl_ast_status_i     ( ast_base_status ),
    .usbdev_usb_ref_val_o         (                 ),
    .usbdev_usb_ref_pulse_o       (                 ),
    .flash_bist_enable_i          ( 1'b0            ),
    .flash_power_down_h_i         ( 1'b0            ),
    .flash_power_ready_h_i        ( 1'b1            ),
    .flash_test_mode_a_i          ('0),
    .flash_test_voltage_h_i       ('0),
    .lc_clk_byp_req_o             ( lc_clk_bypass   ),
    .lc_clk_byp_ack_i             ( lc_clk_bypass   ),
    .clks_ast_o                   (                 ),
    .rsts_ast_o                   (                 ),

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

    // Memory attributes
    .ram_1p_cfg_i    ( '0 ),
    .ram_2p_cfg_i    ( '0 ),
    .rom_cfg_i       ( '0 ),

    // DFT signals
    .scan_rst_ni     ( 1'b1             ),
    .scan_en_i       ( 1'b0             ),
    .scanmode_i      ( lc_ctrl_pkg::Off )
  );

  //////////////////////////////////////
  // Generate precise capture trigger //
  //////////////////////////////////////

  // GPIO15 is used as capture trigger.
  localparam int MioIdxTrigger = 15;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;

  for (genvar i = 0; i < pinmux_reg_pkg::NMioPads; i++) begin : gen_mio_out
    if (i == MioIdxTrigger) begin
      // To obtain a more precise capture trigger for side-channel analysis, we only forward the
      // software-controlled capture trigger when the AES module is actually busy (performing
      // either encryption/decryption or clearing internal registers).
      assign mio_out[i] = mio_out_core[i] & ~top_englishbreakfast.clkmgr_aon_idle[clkmgr_pkg::Aes];
    end else begin
      assign mio_out[i] = mio_out_core[i];
    end
  end

  //////////////////////
  // ChipWhisperer IO //
  //////////////////////

  // Clock ouput to capture board.
  assign TIO_CLKOUT = IO_CLK;

  // UART Tx for debugging. The UART itself is connected to the capture board.
  assign IO_UTX_DEBUG = top_englishbreakfast.cio_uart0_tx_d2p;

endmodule : top_englishbreakfast_cw305
