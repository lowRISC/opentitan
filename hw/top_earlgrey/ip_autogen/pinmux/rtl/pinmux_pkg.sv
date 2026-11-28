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
    63'h1000000000000003, // 105: sysrst_ctrl_lid_open
    63'h0002000000000003, // 104: sysrst_ctrl_pwrb_in
    63'h0040000000000003, // 103: sysrst_ctrl_key2_in
    63'h0010000000000003, // 102: sysrst_ctrl_key1_in
    63'h0004000000000003, // 101: sysrst_ctrl_key0_in
    63'h0008000000000003, // 100: sysrst_ctrl_ac_present
    63'h1000000a00000003, //  99: i3c1_rstdet_sda
    63'h0800000500000003, //  98: i3c1_rstdet_scl
    63'h4000000800200003, //  97: i3c0_rstdet_sda
    63'h2000000400400003, //  96: i3c0_rstdet_scl
    63'h0010000000040003, //  95: uart3_rx
    63'h0000400048000003, //  94: uart2_rx
    63'h0040000000004003, //  93: uart1_rx
    63'h0000008000010003, //  92: uart0_rx
    63'h0000000000250003, //  91: spi_device_tpm_csb
    63'h0000000000002003, //  90: spi_device_csb
    63'h0000000000001003, //  89: spi_device_sck
    63'h1001080000000003, //  88: usbdev_sense
    63'h0400000000000003, //  87: sysrst_ctrl_flash_wp_l
    63'h0200000000000003, //  86: sysrst_ctrl_ec_rst_l
    63'h1000000a00000003, //  85: i3c1_sda
    63'h0800000500000003, //  84: i3c1_scl
    63'h4000000800200003, //  83: i3c0_sda
    63'h2000000400400003, //  82: i3c0_scl
    63'h0000200300400003, //  81: i2c2_scl
    63'h0001000300200003, //  80: i2c2_sda
    63'h0800000c00000003, //  79: i2c1_scl
    63'h1000000c00000003, //  78: i2c1_sda
    63'h2000000100400003, //  77: i2c0_scl
    63'h4000000200200003, //  76: i2c0_sda
    63'h2000000000000003, //  75: gpio1_gpio[31]
    63'h1000000000000003, //  74: gpio1_gpio[30]
    63'h0800000000000003, //  73: gpio1_gpio[29]
    63'h4000000000000003, //  72: gpio1_gpio[28]
    63'h2000000000000003, //  71: gpio1_gpio[27]
    63'h1000000000000003, //  70: gpio1_gpio[26]
    63'h0800000000000003, //  69: gpio1_gpio[25]
    63'h0400000000000003, //  68: gpio1_gpio[24]
    63'h0200000000000003, //  67: gpio1_gpio[23]
    63'h0100000000000003, //  66: gpio1_gpio[22]
    63'h0080000000000003, //  65: gpio1_gpio[21]
    63'h0040000000000003, //  64: gpio1_gpio[20]
    63'h0020000000000003, //  63: gpio1_gpio[19]
    63'h0010000000000003, //  62: gpio1_gpio[18]
    63'h0008000000000003, //  61: gpio1_gpio[17]
    63'h0004000000000003, //  60: gpio1_gpio[16]
    63'h0002000000000003, //  59: gpio1_gpio[15]
    63'h0001000000000003, //  58: gpio1_gpio[14]
    63'h0000800000000003, //  57: gpio1_gpio[13]
    63'h0000400000000003, //  56: gpio1_gpio[12]
    63'h0000200000000003, //  55: gpio1_gpio[11]
    63'h0000100000000003, //  54: gpio1_gpio[10]
    63'h0000080000000003, //  53: gpio1_gpio[9]
    63'h0000040000000003, //  52: gpio1_gpio[8]
    63'h0000020000000003, //  51: gpio1_gpio[7]
    63'h0000010000000003, //  50: gpio1_gpio[6]
    63'h0000008000000003, //  49: gpio1_gpio[5]
    63'h0000004000000003, //  48: gpio1_gpio[4]
    63'h0000002000000003, //  47: gpio1_gpio[3]
    63'h0000001000000003, //  46: gpio1_gpio[2]
    63'h0000000800000003, //  45: gpio1_gpio[1]
    63'h0000000400000003, //  44: gpio1_gpio[0]
    63'h0000000200000003, //  43: gpio0_gpio[31]
    63'h0000000100000003, //  42: gpio0_gpio[30]
    63'h0000000080000003, //  41: gpio0_gpio[29]
    63'h0000000040000003, //  40: gpio0_gpio[28]
    63'h0000000020000003, //  39: gpio0_gpio[27]
    63'h0000000010000003, //  38: gpio0_gpio[26]
    63'h0000000008000003, //  37: gpio0_gpio[25]
    63'h0000000004000003, //  36: gpio0_gpio[24]
    63'h0000000002000003, //  35: gpio0_gpio[23]
    63'h0000000001000003, //  34: gpio0_gpio[22]
    63'h0000000000800003, //  33: gpio0_gpio[21]
    63'h0000000000400003, //  32: gpio0_gpio[20]
    63'h0000000000200003, //  31: gpio0_gpio[19]
    63'h0000000000100003, //  30: gpio0_gpio[18]
    63'h0000000000080003, //  29: gpio0_gpio[17]
    63'h0000000000040003, //  28: gpio0_gpio[16]
    63'h0000000000020003, //  27: gpio0_gpio[15]
    63'h0000000000010003, //  26: gpio0_gpio[14]
    63'h0000000000008003, //  25: gpio0_gpio[13]
    63'h0000000000004003, //  24: gpio0_gpio[12]
    63'h0000000000002003, //  23: gpio0_gpio[11]
    63'h0000000000001003, //  22: gpio0_gpio[10]
    63'h0000000000000803, //  21: gpio0_gpio[9]
    63'h0000000000000403, //  20: gpio0_gpio[8]
    63'h0000000000000203, //  19: gpio0_gpio[7]
    63'h0000000000000103, //  18: gpio0_gpio[6]
    63'h0000000000000083, //  17: gpio0_gpio[5]
    63'h0000000000000043, //  16: gpio0_gpio[4]
    63'h0000000000000023, //  15: gpio0_gpio[3]
    63'h0000000000000013, //  14: gpio0_gpio[2]
    63'h000000000000000b, //  13: gpio0_gpio[1]
    63'h0000000000000007, //  12: gpio0_gpio[0]
    63'h0000000000000803, //  11: spi_device_sd[3]
    63'h0000000000000403, //  10: spi_device_sd[2]
    63'h0000000000000203, //   9: spi_device_sd[1]
    63'h0000000000000103, //   8: spi_device_sd[0]
    63'h0000000020000003, //   7: spi_host1_sd[3]
    63'h0000000008000003, //   6: spi_host1_sd[2]
    63'h0000000002000003, //   5: spi_host1_sd[1]
    63'h0000000001000003, //   4: spi_host1_sd[0]
    63'h0000000000000023, //   3: spi_host0_sd[3]
    63'h0000000000000013, //   2: spi_host0_sd[2]
    63'h000000000000000b, //   1: spi_host0_sd[1]
    63'h0000000000000007  //   0: spi_host0_sd[0]
  };

  // Legal MIO_OUTSEL values for each MIO pad. LSB corresponds to lowest index. Includes static
  // options.
  parameter logic [NMioPads-1:0][NMioPeriphOut+2:0] MioOutselLegal = {
    119'h080000004088000000000000000007, // 60: IOR13
    119'h020000002144000000000000000007, // 59: IOR12
    119'h000000010222000000000000000007, // 58: IOR11
    119'h200000008411000000000000000007, // 57: IOR10
    119'h000000040000800000000000000007, // 56: IOR9
    119'h000000020000400000000000000007, // 55: IOR8
    119'h100080000000200000000000000007, // 54: IOR7
    119'h040010000000100000000000000007, // 53: IOR6
    119'h000000000000080000000000000007, // 52: IOR5
    119'h400040000000040000000000000007, // 51: IOR4
    119'h000000000000020000000000000007, // 50: IOR3
    119'h000100000000010000000000000007, // 49: IOR2
    119'h000000000000008000000000000007, // 48: IOR1
    119'h000000000000004000000000000007, // 47: IOR0
    119'h000000000800002000000000000007, // 46: IOC12
    119'h000020000000001000000000000007, // 45: IOC11
    119'h000000000000000800000000000007, // 44: IOC10
    119'h000000001000000400000000000007, // 43: IOC9
    119'h000000000000000200000000000007, // 42: IOC8
    119'h000000000000000100000000000007, // 41: IOC7
    119'h000000000000000080000000000007, // 40: IOC6
    119'h000000000000000040000000000007, // 39: IOC5
    119'h008008000000000020000000000007, // 38: IOC4
    119'h010000000000000010000000000007, // 37: IOC3
    119'h002000000000000008000000000007, // 36: IOC2
    119'h001000000000000004000000000007, // 35: IOC1
    119'h004000000000000002000000000007, // 34: IOC0
    119'h000000014600000001000000000007, // 33: IOB12
    119'h00000000a600000000800000000007, // 32: IOB11
    119'h000100011880000000400000000007, // 31: IOB10
    119'h000000009900000000200000000007, // 30: IOB9
    119'h000084000000000000100000000007, // 29: IOB8
    119'h000104000000000000080000000007, // 28: IOB7
    119'h000000000000000000040000000407, // 27: IOB6
    119'h000022000000000000020000000007, // 26: IOB5
    119'h000000000000000000010000000207, // 25: IOB4
    119'h000000800000000000008000000007, // 24: IOB3
    119'h000000000000000000004000000107, // 23: IOB2
    119'h000000000000000000002000000087, // 22: IOB1
    119'h000001000000000000001000000007, // 21: IOB0
    119'h000400003100000000000800000007, // 20: IOA8
    119'h000200004880000000000400000007, // 19: IOA7
    119'h000000000000000000000200000007, // 18: IOA6
    119'h000040200000000000000100000007, // 17: IOA5
    119'h000000400000000000000080000007, // 16: IOA4
    119'h000008400000000000000040000007, // 15: IOA3
    119'h000080200000000000000020000007, // 14: IOA2
    119'h000010000000000000000010000007, // 13: IOA1
    119'h000000000000000000000008000007, // 12: IOA0
    119'h000000000000000000000004000007, // 11: SPI_DEV_CS_L
    119'h000000000000000000000002000007, // 10: SPI_DEV_CLK
    119'h000000000000000000000001004007, //  9: SPI_DEV_D3
    119'h000000000000000000000000802007, //  8: SPI_DEV_D2
    119'h000000000000000000000000401007, //  7: SPI_DEV_D1
    119'h000000000000000000000000200807, //  6: SPI_DEV_D0
    119'h000000100000000000000000100007, //  5: SPI_HOST_CS_L
    119'h000000080000000000000000080007, //  4: SPI_HOST_CLK
    119'h000800000000000000000000040047, //  3: SPI_HOST_D3
    119'h000000000000000000000000020027, //  2: SPI_HOST_D2
    119'h000000000000000000000000010017, //  1: SPI_HOST_D1
    119'h00000000000000000000000000800f  //  0: SPI_HOST_D0
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
