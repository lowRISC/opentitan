// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/



module chip_earlgrey_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni
);

  import top_earlgrey_pkg::*;
  import prim_pad_wrapper_pkg::*;

  ////////////////////////////
  // Special Signal Indices //
  ////////////////////////////

  localparam int Tap0PadIdx = 30;
  localparam int Tap1PadIdx = 27;
  localparam int Dft0PadIdx = 40;
  localparam int Dft1PadIdx = 42;
  localparam int TckPadIdx = 38;
  localparam int TmsPadIdx = 35;
  localparam int TrstNPadIdx = 39;
  localparam int TdiPadIdx = 37;
  localparam int TdoPadIdx = 36;

  // DFT and Debug signal positions in the pinout.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    tck_idx:           TckPadIdx,
    tms_idx:           TmsPadIdx,
    trst_idx:          TrstNPadIdx,
    tdi_idx:           TdiPadIdx,
    tdo_idx:           TdoPadIdx,
    tap_strap0_idx:    Tap0PadIdx,
    tap_strap1_idx:    Tap1PadIdx,
    dft_strap0_idx:    Dft0PadIdx,
    dft_strap1_idx:    Dft1PadIdx,
    // TODO: check whether there is a better way to pass these USB-specific params
    usb_dp_idx:        DioUsbdevUsbDp,
    usb_dn_idx:        DioUsbdevUsbDn,
    usb_sense_idx:     MioInUsbdevSense,
    // Pad types for attribute WARL behavior
    dio_pad_type: {
      BidirStd, // DIO spi_host0_csb
      BidirStd, // DIO spi_host0_sck
      InputStd, // DIO spi_device_csb
      InputStd, // DIO spi_device_sck
      BidirOd, // DIO sysrst_ctrl_flash_wp_l
      BidirOd, // DIO sysrst_ctrl_ec_rst_l
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO usbdev_usb_dn
      BidirStd  // DIO usbdev_usb_dp
    },
    mio_pad_type: {
      BidirOd, // MIO Pad 46
      BidirOd, // MIO Pad 45
      BidirOd, // MIO Pad 44
      BidirOd, // MIO Pad 43
      BidirStd, // MIO Pad 42
      BidirStd, // MIO Pad 41
      BidirStd, // MIO Pad 40
      BidirStd, // MIO Pad 39
      BidirStd, // MIO Pad 38
      BidirStd, // MIO Pad 37
      BidirStd, // MIO Pad 36
      BidirStd, // MIO Pad 35
      BidirOd, // MIO Pad 34
      BidirOd, // MIO Pad 33
      BidirOd, // MIO Pad 32
      BidirStd, // MIO Pad 31
      BidirStd, // MIO Pad 30
      BidirStd, // MIO Pad 29
      BidirStd, // MIO Pad 28
      BidirStd, // MIO Pad 27
      BidirStd, // MIO Pad 26
      BidirStd, // MIO Pad 25
      BidirStd, // MIO Pad 24
      BidirStd, // MIO Pad 23
      BidirStd, // MIO Pad 22
      BidirOd, // MIO Pad 21
      BidirOd, // MIO Pad 20
      BidirOd, // MIO Pad 19
      BidirOd, // MIO Pad 18
      BidirStd, // MIO Pad 17
      BidirStd, // MIO Pad 16
      BidirStd, // MIO Pad 15
      BidirStd, // MIO Pad 14
      BidirStd, // MIO Pad 13
      BidirStd, // MIO Pad 12
      BidirStd, // MIO Pad 11
      BidirStd, // MIO Pad 10
      BidirStd, // MIO Pad 9
      BidirOd, // MIO Pad 8
      BidirOd, // MIO Pad 7
      BidirOd, // MIO Pad 6
      BidirStd, // MIO Pad 5
      BidirStd, // MIO Pad 4
      BidirStd, // MIO Pad 3
      BidirStd, // MIO Pad 2
      BidirStd, // MIO Pad 1
      BidirStd  // MIO Pad 0
    },
    // Pad scan roles
    dio_scan_role: {
      scan_role_pkg::DioPadSpiHostCsLScanRole, // DIO spi_host0_csb
      scan_role_pkg::DioPadSpiHostClkScanRole, // DIO spi_host0_sck
      scan_role_pkg::DioPadSpiDevCsLScanRole, // DIO spi_device_csb
      scan_role_pkg::DioPadSpiDevClkScanRole, // DIO spi_device_sck
      scan_role_pkg::DioPadIor9ScanRole, // DIO sysrst_ctrl_flash_wp_l
      scan_role_pkg::DioPadIor8ScanRole, // DIO sysrst_ctrl_ec_rst_l
      scan_role_pkg::DioPadSpiDevD3ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD2ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD1ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD0ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiHostD3ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD2ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD1ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD0ScanRole, // DIO spi_host0_sd
      NoScan, // DIO usbdev_usb_dn
      NoScan // DIO usbdev_usb_dp
    },
    mio_scan_role: {
      scan_role_pkg::MioPadIor13ScanRole,
      scan_role_pkg::MioPadIor12ScanRole,
      scan_role_pkg::MioPadIor11ScanRole,
      scan_role_pkg::MioPadIor10ScanRole,
      scan_role_pkg::MioPadIor7ScanRole,
      scan_role_pkg::MioPadIor6ScanRole,
      scan_role_pkg::MioPadIor5ScanRole,
      scan_role_pkg::MioPadIor4ScanRole,
      scan_role_pkg::MioPadIor3ScanRole,
      scan_role_pkg::MioPadIor2ScanRole,
      scan_role_pkg::MioPadIor1ScanRole,
      scan_role_pkg::MioPadIor0ScanRole,
      scan_role_pkg::MioPadIoc12ScanRole,
      scan_role_pkg::MioPadIoc11ScanRole,
      scan_role_pkg::MioPadIoc10ScanRole,
      scan_role_pkg::MioPadIoc9ScanRole,
      scan_role_pkg::MioPadIoc8ScanRole,
      scan_role_pkg::MioPadIoc7ScanRole,
      scan_role_pkg::MioPadIoc6ScanRole,
      scan_role_pkg::MioPadIoc5ScanRole,
      scan_role_pkg::MioPadIoc4ScanRole,
      scan_role_pkg::MioPadIoc3ScanRole,
      scan_role_pkg::MioPadIoc2ScanRole,
      scan_role_pkg::MioPadIoc1ScanRole,
      scan_role_pkg::MioPadIoc0ScanRole,
      scan_role_pkg::MioPadIob12ScanRole,
      scan_role_pkg::MioPadIob11ScanRole,
      scan_role_pkg::MioPadIob10ScanRole,
      scan_role_pkg::MioPadIob9ScanRole,
      scan_role_pkg::MioPadIob8ScanRole,
      scan_role_pkg::MioPadIob7ScanRole,
      scan_role_pkg::MioPadIob6ScanRole,
      scan_role_pkg::MioPadIob5ScanRole,
      scan_role_pkg::MioPadIob4ScanRole,
      scan_role_pkg::MioPadIob3ScanRole,
      scan_role_pkg::MioPadIob2ScanRole,
      scan_role_pkg::MioPadIob1ScanRole,
      scan_role_pkg::MioPadIob0ScanRole,
      scan_role_pkg::MioPadIoa8ScanRole,
      scan_role_pkg::MioPadIoa7ScanRole,
      scan_role_pkg::MioPadIoa6ScanRole,
      scan_role_pkg::MioPadIoa5ScanRole,
      scan_role_pkg::MioPadIoa4ScanRole,
      scan_role_pkg::MioPadIoa3ScanRole,
      scan_role_pkg::MioPadIoa2ScanRole,
      scan_role_pkg::MioPadIoa1ScanRole,
      scan_role_pkg::MioPadIoa0ScanRole
    }
  };

  ////////////////////////
  // Signal definitions //
  ////////////////////////


  pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr;
  pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr;

  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;


  // Power state from AST to USB
  ast_pkg::ast_pwst_t ast_pwst_h;

  // AST ADC analog inputs and direct analog pad-short outputs.
  ast_pkg::awire_t ast_adc_a0_a, ast_adc_a1_a;
  ast_pkg::awire_t ast2pad_t0_a, ast2pad_t1_a;
  // Tie-off ADC inputs. Leave the direct pad-short outputs unused.
  assign ast_adc_a0_a = '0;
  assign ast_adc_a1_a = '0;
  logic unused_ast_analog;
  assign unused_ast_analog = ^{ast2pad_t0_a, ast2pad_t1_a};

  //////////////////////
  // Padring Instance //
  //////////////////////

  // AST signals needed in padring - must be decleared here
  logic padring_scan_clk;
  prim_mubi_pkg::mubi4_t scanmode;

  // Padring substitute for the Verilator simulation top. The flat
  // per-peripheral cio_* signals live inside padring_verilator and
  // are driven and observed by the testbench DPI models through
  // hierarchical references (XMR).

  // USB signals routed directly to/from top_earlgrey (not via mio/dio)
  logic usb_dp_pullup_en;
  logic usb_dn_pullup_en;
  logic usb_rx_d;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_use_d_se0;
  logic usb_rx_enable;

  padring_verilator u_padring (
    .mio_in_o  (mio_in ),
    .mio_out_i (mio_out),
    .mio_oe_i  (mio_oe ),
    .mio_attr_i(mio_attr),
    .dio_attr_i(dio_attr),

    .dio_in_o (dio_in ),
    .dio_out_i(dio_out),
    .dio_oe_i (dio_oe ),

    .usb_rx_d_o        (usb_rx_d        ),
    .usb_tx_d_i        (usb_tx_d        ),
    .usb_tx_se0_i      (usb_tx_se0      ),
    .usb_tx_use_d_se0_i(usb_tx_use_d_se0),
    .usb_rx_enable_i   (usb_rx_enable   ),
    .usb_dp_pullup_en_i(usb_dp_pullup_en),
    .usb_dn_pullup_en_i(usb_dn_pullup_en)
  );


  ////////////////////////
  // AST related wiring //
  ////////////////////////
  logic clk_ast_ext;
  prim_mubi_pkg::mubi4_t cg_en_ast_ext;
  // This clock gate is never used inside the top. It is a topgen artifact of an external clock.
  assign cg_en_ast_ext = prim_mubi_pkg::MuBi4False;

  ast_pkg::clks_osc_byp_t clks_osc_byp;

  // Debug connections
  logic [ast_pkg::Pad2AstInWidth-1:0] padmux2ast;

  assign clk_ast_ext = '0;
  assign padmux2ast = '0; // TODO: check how to handle this.

  // AON clock divider. Reset is not used because Verilator uses only sync
  // resets (and does not model 'x'); if the divider below were reset, clk_aon
  // would be silenced and the clk_aon logic inside top_earlgrey would not
  // get reset.

  logic clk_aon;
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

  // POR for the AST comes directly from the reset input.
  logic rst_n;
  assign rst_n = rst_ni;

  assign clks_osc_byp = '{
    usb: clk_i,
    sys: clk_i,
    io:  clk_i,
    aon: clk_aon
  };

  // Target (Verilator) specific supply manipulation to create a synthetic POR condition.
  logic [3:0] cnt;
  logic vcc_supp;
  // keep incrementing until saturation
  always_ff @(posedge clk_aon) begin
    if (cnt < 4'hf) begin
      cnt <= cnt + 1'b1;
    end
  end
  assign vcc_supp = cnt < 4'h4 ? 1'b0 :
                    cnt < 4'h8 ? 1'b1 :
                    cnt < 4'hc ? 1'b0 : 1'b1;


  // Tie-off supply voltage test signals
  ast_pkg::ast_vx_supp_t ast_vx_supp;
  assign ast_vx_supp = '{
    vcc:    vcc_supp,
    vcaon:  1'b1,
    vcmain: 1'b1,
    vioa:   1'b1,
    viob:   1'b1
  };

  // flash observation (only for englishbreakfast)
  logic [7:0] flash_obs;
  assign flash_obs = '0;

  // Tie-off observation signals
  ast_pkg::ast_obs_bus_t ast_obs;
  assign ast_obs = '{
    fla_obs: flash_obs,
    otp_obs: '0,
    otm_obs: '0,
    usb_obs: '0
  };

  // Feed the same bypass struct to both PDs. This is a limitation as topgen cannot distribute the
  // same external signal to multiple IP ports from the top. The 'top' signals are local to their
  // power domain. Note these are only relevant for FPGA and verilator. But we always connect them
  // as topgen does not support conditional port generation.
  ast_pkg::clks_osc_byp_t clk_osc_byp_pd_main;
  ast_pkg::clks_osc_byp_t clk_osc_byp_pd_aon;
  assign clk_osc_byp_pd_main = clks_osc_byp;
  assign clk_osc_byp_pd_aon  = clks_osc_byp;

  // AST power states are unused
  logic unused_ast_pwst_h;
  assign unused_ast_pwst_h = ^ast_pwst_h;
  ///////////////////////////////////////
  // top_earlgrey: power domains //
  ///////////////////////////////////////
  top_earlgrey #(
    .SramCtrlRetInstrExec(0),
    .SecAesAllowForcingMasks(1'b1),
    .SramCtrlMainInstrExec(1),
    .PinmuxTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    // Unmanaged external clocks
    .clk_ast_ext_i  (clk_ast_ext),
    .cg_en_ast_ext_i(cg_en_ast_ext),

    // Manual DFT signals
    .padring_scan_clk_o(padring_scan_clk),

    // Multiplexed I/O
    .mio_in_i (mio_in ),
    .mio_out_o(mio_out),
    .mio_oe_o (mio_oe ),

    // Dedicated I/O
    .dio_in_i (dio_in ),
    .dio_out_o(dio_out),
    .dio_oe_o (dio_oe ),

    // Pad attributes
    .mio_attr_o(mio_attr),
    .dio_attr_o(dio_attr),

    // Regular ports (auto-generated)
    .manual_in_por_n_i            (rst_n              ),
    .scanmode_o                   (scanmode           ),
    .scan_en_o                    (                   ),
    .scan_rst_n_o                 (                   ),
    .usb_io_pu_cal_o              (                   ),
    .padmux2ast_i                 (padmux2ast         ),
    .mux_iob_sel_o                (                   ),
    .ast_vx_supp_i                (ast_vx_supp        ),
    .ast_obs_i                    (ast_obs            ),
    .ast_adc_a0_a_i               (ast_adc_a0_a       ),
    .ast_adc_a1_a_i               (ast_adc_a1_a       ),
    .ast2pad_t0_a_o               (ast2pad_t0_a       ),
    .ast2pad_t1_a_o               (ast2pad_t1_a       ),
    .clk_osc_byp_pd_main_i        (clk_osc_byp_pd_main),
    .clk_osc_byp_pd_aon_i         (clk_osc_byp_pd_aon ),
    .ast_pwst_h_o                 (ast_pwst_h         ),
    .dft_hold_tap_sel_i           ('0                 ),
    .usb_dp_pullup_en_o           (usb_dp_pullup_en   ),
    .usb_dn_pullup_en_o           (usb_dn_pullup_en   ),
    .rram_test_analog_io          (                   ),
    .fpga_info_i                  ('0                 ),
    .sensor_ctrl_manual_pad_attr_o(                   ),
    .usbdev_usb_rx_d_i            (usb_rx_d           ),
    .usbdev_usb_tx_d_o            (usb_tx_d           ),
    .usbdev_usb_tx_se0_o          (usb_tx_se0         ),
    .usbdev_usb_tx_use_d_se0_o    (usb_tx_use_d_se0   ),
    .usbdev_usb_rx_enable_o       (usb_rx_enable      )
  );

endmodule
