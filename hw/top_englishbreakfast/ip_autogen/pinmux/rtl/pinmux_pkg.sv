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
    49'h1ffffffffffff, // 37: usbdev_sense
    49'h1ffffffffffff, // 36: flash_ctrl_tdi
    49'h1ffffffffffff, // 35: flash_ctrl_tms
    49'h1ffffffffffff, // 34: flash_ctrl_tck
    49'h1ffffffffffff, // 33: uart1_rx
    49'h1ffffffffffff, // 32: uart0_rx
    49'h1ffffffffffff, // 31: gpio0_gpio[31]
    49'h1ffffffffffff, // 30: gpio0_gpio[30]
    49'h1ffffffffffff, // 29: gpio0_gpio[29]
    49'h1ffffffffffff, // 28: gpio0_gpio[28]
    49'h1ffffffffffff, // 27: gpio0_gpio[27]
    49'h1ffffffffffff, // 26: gpio0_gpio[26]
    49'h1ffffffffffff, // 25: gpio0_gpio[25]
    49'h1ffffffffffff, // 24: gpio0_gpio[24]
    49'h1ffffffffffff, // 23: gpio0_gpio[23]
    49'h1ffffffffffff, // 22: gpio0_gpio[22]
    49'h1ffffffffffff, // 21: gpio0_gpio[21]
    49'h1ffffffffffff, // 20: gpio0_gpio[20]
    49'h1ffffffffffff, // 19: gpio0_gpio[19]
    49'h1ffffffffffff, // 18: gpio0_gpio[18]
    49'h1ffffffffffff, // 17: gpio0_gpio[17]
    49'h1ffffffffffff, // 16: gpio0_gpio[16]
    49'h1ffffffffffff, // 15: gpio0_gpio[15]
    49'h1ffffffffffff, // 14: gpio0_gpio[14]
    49'h1ffffffffffff, // 13: gpio0_gpio[13]
    49'h1ffffffffffff, // 12: gpio0_gpio[12]
    49'h1ffffffffffff, // 11: gpio0_gpio[11]
    49'h1ffffffffffff, // 10: gpio0_gpio[10]
    49'h1ffffffffffff, //  9: gpio0_gpio[9]
    49'h1ffffffffffff, //  8: gpio0_gpio[8]
    49'h1ffffffffffff, //  7: gpio0_gpio[7]
    49'h1ffffffffffff, //  6: gpio0_gpio[6]
    49'h1ffffffffffff, //  5: gpio0_gpio[5]
    49'h1ffffffffffff, //  4: gpio0_gpio[4]
    49'h1ffffffffffff, //  3: gpio0_gpio[3]
    49'h1ffffffffffff, //  2: gpio0_gpio[2]
    49'h1ffffffffffff, //  1: gpio0_gpio[1]
    49'h1ffffffffffff  //  0: gpio0_gpio[0]
  };

  // Legal MIO_OUTSEL values for each MIO pad. LSB corresponds to lowest index. Includes static
  // options.
  parameter logic [NMioPads-1:0][NMioPeriphOut+2:0] MioOutselLegal = {
    38'h3fffffffff, // 46: IOR13
    38'h3fffffffff, // 45: IOR12
    38'h3fffffffff, // 44: IOR11
    38'h3fffffffff, // 43: IOR10
    38'h3fffffffff, // 42: IOR7
    38'h3fffffffff, // 41: IOR6
    38'h3fffffffff, // 40: IOR5
    38'h3fffffffff, // 39: IOR4
    38'h3fffffffff, // 38: IOR3
    38'h3fffffffff, // 37: IOR2
    38'h3fffffffff, // 36: IOR1
    38'h3fffffffff, // 35: IOR0
    38'h3fffffffff, // 34: IOC12
    38'h3fffffffff, // 33: IOC11
    38'h3fffffffff, // 32: IOC10
    38'h3fffffffff, // 31: IOC9
    38'h3fffffffff, // 30: IOC8
    38'h3fffffffff, // 29: IOC7
    38'h3fffffffff, // 28: IOC6
    38'h3fffffffff, // 27: IOC5
    38'h3fffffffff, // 26: IOC4
    38'h3fffffffff, // 25: IOC3
    38'h3fffffffff, // 24: IOC2
    38'h3fffffffff, // 23: IOC1
    38'h3fffffffff, // 22: IOC0
    38'h3fffffffff, // 21: IOB12
    38'h3fffffffff, // 20: IOB11
    38'h3fffffffff, // 19: IOB10
    38'h3fffffffff, // 18: IOB9
    38'h3fffffffff, // 17: IOB8
    38'h3fffffffff, // 16: IOB7
    38'h3fffffffff, // 15: IOB6
    38'h3fffffffff, // 14: IOB5
    38'h3fffffffff, // 13: IOB4
    38'h3fffffffff, // 12: IOB3
    38'h3fffffffff, // 11: IOB2
    38'h3fffffffff, // 10: IOB1
    38'h3fffffffff, //  9: IOB0
    38'h3fffffffff, //  8: IOA8
    38'h3fffffffff, //  7: IOA7
    38'h3fffffffff, //  6: IOA6
    38'h3fffffffff, //  5: IOA5
    38'h3fffffffff, //  4: IOA4
    38'h3fffffffff, //  3: IOA3
    38'h3fffffffff, //  2: IOA2
    38'h3fffffffff, //  1: IOA1
    38'h3fffffffff  //  0: IOA0
  };

  // Reset values of the MIO_PAD_ATTR CSRs defined by the top. LSB corresponds to lowest index.
  parameter pad_attr_t [NMioPads-1:0] MioPadAttrResval = {
    pad_attr_t'{default: '0}, // 46: IOR13
    pad_attr_t'{default: '0}, // 45: IOR12
    pad_attr_t'{default: '0}, // 44: IOR11
    pad_attr_t'{default: '0}, // 43: IOR10
    pad_attr_t'{default: '0}, // 42: IOR7
    pad_attr_t'{default: '0}, // 41: IOR6
    pad_attr_t'{default: '0}, // 40: IOR5
    pad_attr_t'{default: '0}, // 39: IOR4
    pad_attr_t'{default: '0}, // 38: IOR3
    pad_attr_t'{default: '0}, // 37: IOR2
    pad_attr_t'{default: '0}, // 36: IOR1
    pad_attr_t'{default: '0}, // 35: IOR0
    pad_attr_t'{default: '0}, // 34: IOC12
    pad_attr_t'{default: '0}, // 33: IOC11
    pad_attr_t'{default: '0}, // 32: IOC10
    pad_attr_t'{default: '0}, // 31: IOC9
    pad_attr_t'{pull_en: 1'h1, default: '0}, // 30: IOC8
    pad_attr_t'{default: '0}, // 29: IOC7
    pad_attr_t'{default: '0}, // 28: IOC6
    pad_attr_t'{default: '0}, // 27: IOC5
    pad_attr_t'{default: '0}, // 26: IOC4
    pad_attr_t'{default: '0}, // 25: IOC3
    pad_attr_t'{default: '0}, // 24: IOC2
    pad_attr_t'{default: '0}, // 23: IOC1
    pad_attr_t'{default: '0}, // 22: IOC0
    pad_attr_t'{default: '0}, // 21: IOB12
    pad_attr_t'{default: '0}, // 20: IOB11
    pad_attr_t'{default: '0}, // 19: IOB10
    pad_attr_t'{default: '0}, // 18: IOB9
    pad_attr_t'{default: '0}, // 17: IOB8
    pad_attr_t'{default: '0}, // 16: IOB7
    pad_attr_t'{default: '0}, // 15: IOB6
    pad_attr_t'{default: '0}, // 14: IOB5
    pad_attr_t'{default: '0}, // 13: IOB4
    pad_attr_t'{default: '0}, // 12: IOB3
    pad_attr_t'{default: '0}, // 11: IOB2
    pad_attr_t'{default: '0}, // 10: IOB1
    pad_attr_t'{default: '0}, //  9: IOB0
    pad_attr_t'{default: '0}, //  8: IOA8
    pad_attr_t'{default: '0}, //  7: IOA7
    pad_attr_t'{default: '0}, //  6: IOA6
    pad_attr_t'{default: '0}, //  5: IOA5
    pad_attr_t'{default: '0}, //  4: IOA4
    pad_attr_t'{default: '0}, //  3: IOA3
    pad_attr_t'{default: '0}, //  2: IOA2
    pad_attr_t'{default: '0}, //  1: IOA1
    pad_attr_t'{default: '0}  //  0: IOA0
  };

  // Reset values of the DIO_PAD_ATTR CSRs defined by the top. LSB corresponds to lowest index.
  parameter pad_attr_t [NDioPads-1:0] DioPadAttrResval = {
    pad_attr_t'{default: '0}, // 13: SPI_HOST_CS_L
    pad_attr_t'{default: '0}, // 12: SPI_HOST_CLK
    pad_attr_t'{default: '0}, // 11: SPI_DEV_CS_L
    pad_attr_t'{default: '0}, // 10: SPI_DEV_CLK
    pad_attr_t'{default: '0}, //  9: usbdev_usb_dn
    pad_attr_t'{default: '0}, //  8: usbdev_usb_dp
    pad_attr_t'{default: '0}, //  7: SPI_DEV_D3
    pad_attr_t'{default: '0}, //  6: SPI_DEV_D2
    pad_attr_t'{default: '0}, //  5: SPI_DEV_D1
    pad_attr_t'{default: '0}, //  4: SPI_DEV_D0
    pad_attr_t'{default: '0}, //  3: SPI_HOST_D3
    pad_attr_t'{default: '0}, //  2: SPI_HOST_D2
    pad_attr_t'{default: '0}, //  1: SPI_HOST_D1
    pad_attr_t'{default: '0}  //  0: SPI_HOST_D0
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
