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
    pad_type_e [NDioPads-1:0] dio_pad_type;
    pad_type_e [NMioPads-1:0] mio_pad_type;
    scan_role_e [NDioPads-1:0] dio_scan_role;
    scan_role_e [NMioPads-1:0] mio_scan_role;
  } target_cfg_t;

  parameter target_cfg_t DefaultTargetCfg = '{
    dio_pad_type:      {NDioPads{BidirStd}},
    mio_pad_type:      {NMioPads{BidirStd}},
    dio_scan_role:     {NDioPads{NoScan}},
    mio_scan_role:     {NMioPads{NoScan}}
  };

  // Reset values of the MIO_PAD_ATTR CSRs defined by the top. LSB corresponds to lowest index.
  parameter pad_attr_t [NMioPads-1:0] MioPadAttrResval = {
    pad_attr_t'{default: '0}, // 11: MIO11
    pad_attr_t'{default: '0}, // 10: MIO10
    pad_attr_t'{default: '0}, //  9: MIO9
    pad_attr_t'{default: '0}, //  8: MIO8
    pad_attr_t'{default: '0}, //  7: MIO7
    pad_attr_t'{default: '0}, //  6: MIO6
    pad_attr_t'{default: '0}, //  5: MIO5
    pad_attr_t'{default: '0}, //  4: MIO4
    pad_attr_t'{default: '0}, //  3: MIO3
    pad_attr_t'{default: '0}, //  2: MIO2
    pad_attr_t'{default: '0}, //  1: MIO1
    pad_attr_t'{default: '0}  //  0: MIO0
  };

  // Reset values of the DIO_PAD_ATTR CSRs defined by the top. LSB corresponds to lowest index.
  parameter pad_attr_t [NDioPads-1:0] DioPadAttrResval = {
    pad_attr_t'{default: '0}, // 72: SOC_GPO11
    pad_attr_t'{default: '0}, // 71: SOC_GPO10
    pad_attr_t'{default: '0}, // 70: SOC_GPO9
    pad_attr_t'{default: '0}, // 69: SOC_GPO8
    pad_attr_t'{default: '0}, // 68: SOC_GPO7
    pad_attr_t'{default: '0}, // 67: SOC_GPO6
    pad_attr_t'{default: '0}, // 66: SOC_GPO5
    pad_attr_t'{default: '0}, // 65: SOC_GPO4
    pad_attr_t'{default: '0}, // 64: SOC_GPO3
    pad_attr_t'{default: '0}, // 63: SOC_GPO2
    pad_attr_t'{default: '0}, // 62: SOC_GPO1
    pad_attr_t'{default: '0}, // 61: SOC_GPO0
    pad_attr_t'{default: '0}, // 60: UART_TX
    pad_attr_t'{default: '0}, // 59: SPI_HOST_CS_L
    pad_attr_t'{default: '0}, // 58: SPI_HOST_CLK
    pad_attr_t'{default: '0}, // 57: SOC_GPI11
    pad_attr_t'{default: '0}, // 56: SOC_GPI10
    pad_attr_t'{default: '0}, // 55: SOC_GPI9
    pad_attr_t'{default: '0}, // 54: SOC_GPI8
    pad_attr_t'{default: '0}, // 53: SOC_GPI7
    pad_attr_t'{default: '0}, // 52: SOC_GPI6
    pad_attr_t'{default: '0}, // 51: SOC_GPI5
    pad_attr_t'{default: '0}, // 50: SOC_GPI4
    pad_attr_t'{default: '0}, // 49: SOC_GPI3
    pad_attr_t'{default: '0}, // 48: SOC_GPI2
    pad_attr_t'{default: '0}, // 47: SOC_GPI1
    pad_attr_t'{default: '0}, // 46: SOC_GPI0
    pad_attr_t'{default: '0}, // 45: UART_RX
    pad_attr_t'{default: '0}, // 44: SPI_DEV_TPM_CS_L
    pad_attr_t'{default: '0}, // 43: SPI_DEV_CS_L
    pad_attr_t'{default: '0}, // 42: SPI_DEV_CLK
    pad_attr_t'{default: '0}, // 41: GPIO31
    pad_attr_t'{default: '0}, // 40: GPIO30
    pad_attr_t'{default: '0}, // 39: GPIO29
    pad_attr_t'{default: '0}, // 38: GPIO28
    pad_attr_t'{default: '0}, // 37: GPIO27
    pad_attr_t'{default: '0}, // 36: GPIO26
    pad_attr_t'{default: '0}, // 35: GPIO25
    pad_attr_t'{default: '0}, // 34: GPIO24
    pad_attr_t'{default: '0}, // 33: GPIO23
    pad_attr_t'{default: '0}, // 32: GPIO22
    pad_attr_t'{default: '0}, // 31: GPIO21
    pad_attr_t'{default: '0}, // 30: GPIO20
    pad_attr_t'{default: '0}, // 29: GPIO19
    pad_attr_t'{default: '0}, // 28: GPIO18
    pad_attr_t'{default: '0}, // 27: GPIO17
    pad_attr_t'{default: '0}, // 26: GPIO16
    pad_attr_t'{default: '0}, // 25: GPIO15
    pad_attr_t'{default: '0}, // 24: GPIO14
    pad_attr_t'{default: '0}, // 23: GPIO13
    pad_attr_t'{default: '0}, // 22: GPIO12
    pad_attr_t'{default: '0}, // 21: GPIO11
    pad_attr_t'{default: '0}, // 20: GPIO10
    pad_attr_t'{default: '0}, // 19: GPIO9
    pad_attr_t'{default: '0}, // 18: GPIO8
    pad_attr_t'{default: '0}, // 17: GPIO7
    pad_attr_t'{default: '0}, // 16: GPIO6
    pad_attr_t'{default: '0}, // 15: GPIO5
    pad_attr_t'{default: '0}, // 14: GPIO4
    pad_attr_t'{default: '0}, // 13: GPIO3
    pad_attr_t'{default: '0}, // 12: GPIO2
    pad_attr_t'{default: '0}, // 11: GPIO1
    pad_attr_t'{default: '0}, // 10: GPIO0
    pad_attr_t'{default: '0}, //  9: I2C_SDA
    pad_attr_t'{default: '0}, //  8: I2C_SCL
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
