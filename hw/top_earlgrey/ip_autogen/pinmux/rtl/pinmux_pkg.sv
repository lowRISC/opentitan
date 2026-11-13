// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pinmux_pkg;

  import pinmux_reg_pkg::*;
  import prim_pad_wrapper_pkg::*;

  parameter int NumIOs     = NMioPads + NDioPads;
  parameter int NDFTStraps = 2;
  parameter int NTapStraps = 2;

  // Since the target-specific top-levels often have slightly different debug signal positions, we
  // need a way to pass this info from the target specific top-level into the pinmux logic. The
  // datastructure below serves this purpose. Note that all the indices below are with respect to
  // the concatenated {DIO, MIO} packed array.
  typedef struct packed {
    integer                   tck_idx;
    integer                   tms_idx;
    integer                   trst_idx;
    integer                   tdi_idx;
    integer                   tdo_idx;
    integer                   tap_strap0_idx;
    integer                   tap_strap1_idx;
    integer                   dft_strap0_idx;
    integer                   dft_strap1_idx;
    integer                   usb_dp_idx;
    integer                   usb_dn_idx;
    integer                   usb_sense_idx;
    pad_type_e [NDioPads-1:0] dio_pad_type;
    pad_type_e [NMioPads-1:0] mio_pad_type;
    scan_role_e [NDioPads-1:0] dio_scan_role;
    scan_role_e [NMioPads-1:0] mio_scan_role;
  } target_cfg_t;

  parameter target_cfg_t DefaultTargetCfg = '{
    tck_idx:           0,
    tms_idx:           0,
    trst_idx:          0,
    tdi_idx:           0,
    tdo_idx:           0,
    tap_strap0_idx:    0,
    tap_strap1_idx:    0,
    dft_strap0_idx:    0,
    dft_strap1_idx:    0,
    usb_dp_idx:        0,
    usb_dn_idx:        0,
    usb_sense_idx:     0,
    dio_pad_type:      {NDioPads{BidirStd}},
    mio_pad_type:      {NMioPads{BidirStd}},
    dio_scan_role:     {NDioPads{NoScan}},
    mio_scan_role:     {NMioPads{NoScan}}
  };

  // Legal MIO_PERIPH_INSEL values for each MIO peripheral input. LSB corresponds to lowest index.
  // Includes static options.
  parameter logic [NMioPeriphIn-1:0][NMioPads+1:0] MioPeriphInselLegal = {
    63'h7fffffffffffffff, // 105: sysrst_ctrl_lid_open
    63'h7fffffffffffffff, // 104: sysrst_ctrl_pwrb_in
    63'h7fffffffffffffff, // 103: sysrst_ctrl_key2_in
    63'h7fffffffffffffff, // 102: sysrst_ctrl_key1_in
    63'h7fffffffffffffff, // 101: sysrst_ctrl_key0_in
    63'h7fffffffffffffff, // 100: sysrst_ctrl_ac_present
    63'h7fffffffffffffff, //  99: spi_device_tpm_csb
    63'h7fffffffffffffff, //  98: i3c1_rstdet_sda
    63'h7fffffffffffffff, //  97: i3c1_rstdet_scl
    63'h7fffffffffffffff, //  96: i3c0_rstdet_sda
    63'h7fffffffffffffff, //  95: i3c0_rstdet_scl
    63'h7fffffffffffffff, //  94: uart3_rx
    63'h7fffffffffffffff, //  93: uart2_rx
    63'h7fffffffffffffff, //  92: uart1_rx
    63'h7fffffffffffffff, //  91: uart0_rx
    63'h0000000000002003, //  90: spi_device_csb
    63'h0000000000001003, //  89: spi_device_sck
    63'h7fffffffffffffff, //  88: usbdev_sense
    63'h0400000000000003, //  87: sysrst_ctrl_flash_wp_l
    63'h0200000000000003, //  86: sysrst_ctrl_ec_rst_l
    63'h7fffffffffffffff, //  85: spi_host1_sd[3]
    63'h7fffffffffffffff, //  84: spi_host1_sd[2]
    63'h7fffffffffffffff, //  83: spi_host1_sd[1]
    63'h7fffffffffffffff, //  82: spi_host1_sd[0]
    63'h7fffffffffffffff, //  81: i3c1_sda
    63'h7fffffffffffffff, //  80: i3c1_scl
    63'h7fffffffffffffff, //  79: i3c0_sda
    63'h7fffffffffffffff, //  78: i3c0_scl
    63'h7fffffffffffffff, //  77: i2c2_scl
    63'h7fffffffffffffff, //  76: i2c2_sda
    63'h7fffffffffffffff, //  75: i2c1_scl
    63'h7fffffffffffffff, //  74: i2c1_sda
    63'h7fffffffffffffff, //  73: i2c0_scl
    63'h7fffffffffffffff, //  72: i2c0_sda
    63'h7fffffffffffffff, //  71: gpio1_gpio[31]
    63'h7fffffffffffffff, //  70: gpio1_gpio[30]
    63'h7fffffffffffffff, //  69: gpio1_gpio[29]
    63'h7fffffffffffffff, //  68: gpio1_gpio[28]
    63'h7fffffffffffffff, //  67: gpio1_gpio[27]
    63'h7fffffffffffffff, //  66: gpio1_gpio[26]
    63'h7fffffffffffffff, //  65: gpio1_gpio[25]
    63'h7fffffffffffffff, //  64: gpio1_gpio[24]
    63'h7fffffffffffffff, //  63: gpio1_gpio[23]
    63'h7fffffffffffffff, //  62: gpio1_gpio[22]
    63'h7fffffffffffffff, //  61: gpio1_gpio[21]
    63'h7fffffffffffffff, //  60: gpio1_gpio[20]
    63'h7fffffffffffffff, //  59: gpio1_gpio[19]
    63'h7fffffffffffffff, //  58: gpio1_gpio[18]
    63'h7fffffffffffffff, //  57: gpio1_gpio[17]
    63'h7fffffffffffffff, //  56: gpio1_gpio[16]
    63'h7fffffffffffffff, //  55: gpio1_gpio[15]
    63'h7fffffffffffffff, //  54: gpio1_gpio[14]
    63'h7fffffffffffffff, //  53: gpio1_gpio[13]
    63'h7fffffffffffffff, //  52: gpio1_gpio[12]
    63'h7fffffffffffffff, //  51: gpio1_gpio[11]
    63'h7fffffffffffffff, //  50: gpio1_gpio[10]
    63'h7fffffffffffffff, //  49: gpio1_gpio[9]
    63'h7fffffffffffffff, //  48: gpio1_gpio[8]
    63'h7fffffffffffffff, //  47: gpio1_gpio[7]
    63'h7fffffffffffffff, //  46: gpio1_gpio[6]
    63'h7fffffffffffffff, //  45: gpio1_gpio[5]
    63'h7fffffffffffffff, //  44: gpio1_gpio[4]
    63'h7fffffffffffffff, //  43: gpio1_gpio[3]
    63'h7fffffffffffffff, //  42: gpio1_gpio[2]
    63'h7fffffffffffffff, //  41: gpio1_gpio[1]
    63'h7fffffffffffffff, //  40: gpio1_gpio[0]
    63'h7fffffffffffffff, //  39: gpio0_gpio[31]
    63'h7fffffffffffffff, //  38: gpio0_gpio[30]
    63'h7fffffffffffffff, //  37: gpio0_gpio[29]
    63'h7fffffffffffffff, //  36: gpio0_gpio[28]
    63'h7fffffffffffffff, //  35: gpio0_gpio[27]
    63'h7fffffffffffffff, //  34: gpio0_gpio[26]
    63'h7fffffffffffffff, //  33: gpio0_gpio[25]
    63'h7fffffffffffffff, //  32: gpio0_gpio[24]
    63'h7fffffffffffffff, //  31: gpio0_gpio[23]
    63'h7fffffffffffffff, //  30: gpio0_gpio[22]
    63'h7fffffffffffffff, //  29: gpio0_gpio[21]
    63'h7fffffffffffffff, //  28: gpio0_gpio[20]
    63'h7fffffffffffffff, //  27: gpio0_gpio[19]
    63'h7fffffffffffffff, //  26: gpio0_gpio[18]
    63'h7fffffffffffffff, //  25: gpio0_gpio[17]
    63'h7fffffffffffffff, //  24: gpio0_gpio[16]
    63'h7fffffffffffffff, //  23: gpio0_gpio[15]
    63'h7fffffffffffffff, //  22: gpio0_gpio[14]
    63'h7fffffffffffffff, //  21: gpio0_gpio[13]
    63'h7fffffffffffffff, //  20: gpio0_gpio[12]
    63'h7fffffffffffffff, //  19: gpio0_gpio[11]
    63'h7fffffffffffffff, //  18: gpio0_gpio[10]
    63'h7fffffffffffffff, //  17: gpio0_gpio[9]
    63'h7fffffffffffffff, //  16: gpio0_gpio[8]
    63'h7fffffffffffffff, //  15: gpio0_gpio[7]
    63'h7fffffffffffffff, //  14: gpio0_gpio[6]
    63'h7fffffffffffffff, //  13: gpio0_gpio[5]
    63'h7fffffffffffffff, //  12: gpio0_gpio[4]
    63'h7fffffffffffffff, //  11: gpio0_gpio[3]
    63'h7fffffffffffffff, //  10: gpio0_gpio[2]
    63'h7fffffffffffffff, //   9: gpio0_gpio[1]
    63'h7fffffffffffffff, //   8: gpio0_gpio[0]
    63'h0000000000000803, //   7: spi_device_sd[3]
    63'h0000000000000403, //   6: spi_device_sd[2]
    63'h0000000000000203, //   5: spi_device_sd[1]
    63'h0000000000000103, //   4: spi_device_sd[0]
    63'h0000000000000023, //   3: spi_host0_sd[3]
    63'h0000000000000013, //   2: spi_host0_sd[2]
    63'h000000000000000b, //   1: spi_host0_sd[1]
    63'h0000000000000007  //   0: spi_host0_sd[0]
  };

  // Legal MIO_OUTSEL values for each MIO pad. LSB corresponds to lowest index. Includes static
  // options.
  parameter logic [NMioPads-1:0][NMioPeriphOut+2:0] MioOutselLegal = {
    119'h7fffffe1fffffffffffffffffff807, // 60: IOR13
    119'h7fffffe1fffffffffffffffffff807, // 59: IOR12
    119'h7fffffe1fffffffffffffffffff807, // 58: IOR11
    119'h7fffffe1fffffffffffffffffff807, // 57: IOR10
    119'h7fffffe5fffffffffffffffffff807, // 56: IOR9
    119'h7fffffe3fffffffffffffffffff807, // 55: IOR8
    119'h7fffffe1fffffffffffffffffff807, // 54: IOR7
    119'h7fffffe1fffffffffffffffffff807, // 53: IOR6
    119'h7fffffe1fffffffffffffffffff807, // 52: IOR5
    119'h7fffffe1fffffffffffffffffff807, // 51: IOR4
    119'h7fffffe1fffffffffffffffffff807, // 50: IOR3
    119'h7fffffe1fffffffffffffffffff807, // 49: IOR2
    119'h7fffffe1fffffffffffffffffff807, // 48: IOR1
    119'h7fffffe1fffffffffffffffffff807, // 47: IOR0
    119'h7fffffe1fffffffffffffffffff807, // 46: IOC12
    119'h7fffffe1fffffffffffffffffff807, // 45: IOC11
    119'h7fffffe1fffffffffffffffffff807, // 44: IOC10
    119'h7fffffe1fffffffffffffffffff807, // 43: IOC9
    119'h7fffffe1fffffffffffffffffff807, // 42: IOC8
    119'h7fffffe1fffffffffffffffffff807, // 41: IOC7
    119'h7fffffe1fffffffffffffffffff807, // 40: IOC6
    119'h7fffffe1fffffffffffffffffff807, // 39: IOC5
    119'h7fffffe1fffffffffffffffffff807, // 38: IOC4
    119'h7fffffe1fffffffffffffffffff807, // 37: IOC3
    119'h7fffffe1fffffffffffffffffff807, // 36: IOC2
    119'h7fffffe1fffffffffffffffffff807, // 35: IOC1
    119'h7fffffe1fffffffffffffffffff807, // 34: IOC0
    119'h7fffffe1fffffffffffffffffff807, // 33: IOB12
    119'h7fffffe1fffffffffffffffffff807, // 32: IOB11
    119'h7fffffe1fffffffffffffffffff807, // 31: IOB10
    119'h7fffffe1fffffffffffffffffff807, // 30: IOB9
    119'h7fffffe1fffffffffffffffffff807, // 29: IOB8
    119'h7fffffe1fffffffffffffffffff807, // 28: IOB7
    119'h7fffffe1fffffffffffffffffff807, // 27: IOB6
    119'h7fffffe1fffffffffffffffffff807, // 26: IOB5
    119'h7fffffe1fffffffffffffffffff807, // 25: IOB4
    119'h7fffffe1fffffffffffffffffff807, // 24: IOB3
    119'h7fffffe1fffffffffffffffffff807, // 23: IOB2
    119'h7fffffe1fffffffffffffffffff807, // 22: IOB1
    119'h7fffffe1fffffffffffffffffff807, // 21: IOB0
    119'h7fffffe1fffffffffffffffffff807, // 20: IOA8
    119'h7fffffe1fffffffffffffffffff807, // 19: IOA7
    119'h7fffffe1fffffffffffffffffff807, // 18: IOA6
    119'h7fffffe1fffffffffffffffffff807, // 17: IOA5
    119'h7fffffe1fffffffffffffffffff807, // 16: IOA4
    119'h7fffffe1fffffffffffffffffff807, // 15: IOA3
    119'h7fffffe1fffffffffffffffffff807, // 14: IOA2
    119'h7fffffe1fffffffffffffffffff807, // 13: IOA1
    119'h7fffffe1fffffffffffffffffff807, // 12: IOA0
    119'h7fffffe1fffffffffffffffffff807, // 11: SPI_DEV_CS_L
    119'h7fffffe1fffffffffffffffffff807, // 10: SPI_DEV_CLK
    119'h7fffffe1fffffffffffffffffffc07, //  9: SPI_DEV_D3
    119'h7fffffe1fffffffffffffffffffa07, //  8: SPI_DEV_D2
    119'h7fffffe1fffffffffffffffffff907, //  7: SPI_DEV_D1
    119'h7fffffe1fffffffffffffffffff887, //  6: SPI_DEV_D0
    119'h7ffffff1fffffffffffffffffff807, //  5: SPI_HOST_CS_L
    119'h7fffffe9fffffffffffffffffff807, //  4: SPI_HOST_CLK
    119'h7fffffe1fffffffffffffffffff847, //  3: SPI_HOST_D3
    119'h7fffffe1fffffffffffffffffff827, //  2: SPI_HOST_D2
    119'h7fffffe1fffffffffffffffffff817, //  1: SPI_HOST_D1
    119'h7fffffe1fffffffffffffffffff80f  //  0: SPI_HOST_D0
  };

  // Reset values of the MIO_PAD_ATTR CSRs defined by the top. LSB corresponds to lowest index.
  parameter pad_attr_t [NMioPads-1:0] MioPadAttrResval = {
    pad_attr_t'{default: '0}, // 60: IOR13
    pad_attr_t'{default: '0}, // 59: IOR12
    pad_attr_t'{default: '0}, // 58: IOR11
    pad_attr_t'{default: '0}, // 57: IOR10
    pad_attr_t'{virt_od_en: 1'h1, default: '0}, // 56: IOR9
    pad_attr_t'{virt_od_en: 1'h1, default: '0}, // 55: IOR8
    pad_attr_t'{default: '0}, // 54: IOR7
    pad_attr_t'{default: '0}, // 53: IOR6
    pad_attr_t'{default: '0}, // 52: IOR5
    pad_attr_t'{default: '0}, // 51: IOR4
    pad_attr_t'{default: '0}, // 50: IOR3
    pad_attr_t'{default: '0}, // 49: IOR2
    pad_attr_t'{default: '0}, // 48: IOR1
    pad_attr_t'{default: '0}, // 47: IOR0
    pad_attr_t'{default: '0}, // 46: IOC12
    pad_attr_t'{default: '0}, // 45: IOC11
    pad_attr_t'{default: '0}, // 44: IOC10
    pad_attr_t'{default: '0}, // 43: IOC9
    pad_attr_t'{pull_en: 1'h1, pull_select: 1'h0, default: '0}, // 42: IOC8
    pad_attr_t'{default: '0}, // 41: IOC7
    pad_attr_t'{default: '0}, // 40: IOC6
    pad_attr_t'{default: '0}, // 39: IOC5
    pad_attr_t'{default: '0}, // 38: IOC4
    pad_attr_t'{default: '0}, // 37: IOC3
    pad_attr_t'{default: '0}, // 36: IOC2
    pad_attr_t'{default: '0}, // 35: IOC1
    pad_attr_t'{default: '0}, // 34: IOC0
    pad_attr_t'{default: '0}, // 33: IOB12
    pad_attr_t'{default: '0}, // 32: IOB11
    pad_attr_t'{default: '0}, // 31: IOB10
    pad_attr_t'{default: '0}, // 30: IOB9
    pad_attr_t'{default: '0}, // 29: IOB8
    pad_attr_t'{default: '0}, // 28: IOB7
    pad_attr_t'{default: '0}, // 27: IOB6
    pad_attr_t'{default: '0}, // 26: IOB5
    pad_attr_t'{default: '0}, // 25: IOB4
    pad_attr_t'{default: '0}, // 24: IOB3
    pad_attr_t'{default: '0}, // 23: IOB2
    pad_attr_t'{default: '0}, // 22: IOB1
    pad_attr_t'{default: '0}, // 21: IOB0
    pad_attr_t'{default: '0}, // 20: IOA8
    pad_attr_t'{default: '0}, // 19: IOA7
    pad_attr_t'{default: '0}, // 18: IOA6
    pad_attr_t'{default: '0}, // 17: IOA5
    pad_attr_t'{default: '0}, // 16: IOA4
    pad_attr_t'{default: '0}, // 15: IOA3
    pad_attr_t'{default: '0}, // 14: IOA2
    pad_attr_t'{default: '0}, // 13: IOA1
    pad_attr_t'{default: '0}, // 12: IOA0
    pad_attr_t'{default: '0}, // 11: SPI_DEV_CS_L
    pad_attr_t'{default: '0}, // 10: SPI_DEV_CLK
    pad_attr_t'{default: '0}, //  9: SPI_DEV_D3
    pad_attr_t'{default: '0}, //  8: SPI_DEV_D2
    pad_attr_t'{default: '0}, //  7: SPI_DEV_D1
    pad_attr_t'{default: '0}, //  6: SPI_DEV_D0
    pad_attr_t'{default: '0}, //  5: SPI_HOST_CS_L
    pad_attr_t'{default: '0}, //  4: SPI_HOST_CLK
    pad_attr_t'{default: '0}, //  3: SPI_HOST_D3
    pad_attr_t'{default: '0}, //  2: SPI_HOST_D2
    pad_attr_t'{default: '0}, //  1: SPI_HOST_D1
    pad_attr_t'{default: '0}  //  0: SPI_HOST_D0
  };

  // Reset values of the DIO_PAD_ATTR CSRs defined by the top. LSB corresponds to lowest index.
  parameter pad_attr_t [NDioPads-1:0] DioPadAttrResval = {
    pad_attr_t'{default: '0}, // 1: usbdev_usb_dn
    pad_attr_t'{default: '0}  // 0: usbdev_usb_dp
  };

  // Wakeup Detector Modes
  typedef enum logic [2:0] {
    Posedge   = 3'b000,
    Negedge   = 3'b001,
    Edge      = 3'b010,
    HighTimed = 3'b011,
    LowTimed  = 3'b100
  } wkup_mode_e;

  // Interface with LC controller
  typedef struct packed {
    logic                  valid;
    logic [NDFTStraps-1:0] straps;
  } dft_strap_test_req_t;

  typedef enum logic [NTapStraps-1:0] {
    FuncSel   = 2'b00,
    LcTapSel  = 2'b01,
    RvTapSel  = 2'b10,
    DftTapSel = 2'b11
  } tap_strap_t;

endpackage : pinmux_pkg
