// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Provides parameters, types and methods shared throughout the chip level testbench.
package chip_common_pkg;

  // Chip composition (number of hardware resources).
  parameter dv_utils_pkg::uint NUM_GPIOS = 16;
  parameter dv_utils_pkg::uint NUM_UARTS = 4;
  parameter dv_utils_pkg::uint NUM_I2CS = 3;
  parameter dv_utils_pkg::uint NUM_PWM_CHANNELS = pwm_reg_pkg::NOutputs;

  // Buffer is half of SPI_DEVICE Dual Port SRAM
  parameter dv_utils_pkg::uint SPI_FRAME_BYTE_SIZE = spi_device_reg_pkg::SPI_DEVICE_BUFFER_SIZE/2;

  // SW constants - use unmapped address space with at least 32 bytes.
  parameter bit [top_pkg::TL_AW-1:0] SW_DV_START_ADDR = tl_main_pkg::ADDR_SPACE_RV_CORE_IBEX__CFG +
      rv_core_ibex_reg_pkg::RV_CORE_IBEX_DV_SIM_WINDOW_OFFSET;

  parameter bit [top_pkg::TL_AW-1:0] SW_DV_TEST_STATUS_ADDR = SW_DV_START_ADDR + 0;
  parameter bit [top_pkg::TL_AW-1:0] SW_DV_LOG_ADDR         = SW_DV_START_ADDR + 4;

  // TODO: Eventually, move everything from chip_env_pkg to here.

  // Chip IOs.
  //
  // This aggregates all chip IOs as seen at the pads.
  typedef enum {
    // Dedicated pads
    PorN,
    UsbP,
    UsbN,
    CC1,
    CC2,
    FlashTestVolt,
    FlashTestMode0,
    FlashTestMode1,
    OtpExtVolt,
    SpiHostD[0:3],
    SpiHostClk,
    SpiHostCsL,
    SpiDevD[0:3],
    SpiDevClk,
    SpiDevCSL,
    AstMisc,

    // Muxed Pads
    IoA[0:8],
    IoB[0:12],
    IoC[0:12],

    // Note: IOR[8:9] are dedicated IOs used by sysrst_ctrl.
    IoR[0:13],

    // Total number of pads, including dedicated and muxed.
    IoNumTotal
  } chip_io_e;

endpackage
