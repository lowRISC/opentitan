// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#if defined(OPENTITAN_IS_EARLGREY)
#include "dt/dt_usbdev.h"                  // Generated
#include "sw/device/lib/dif/dif_usbdev.h"  // Generated

#include "usbdev_regs.h"  // Generated
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling does not have a USB device
#else
#error "rstmgr_sw_rst_ctrl_test does not support this top"
#endif

#include "dt/dt_i2c.h"         // Generated
#include "dt/dt_rstmgr.h"      // Generated
#include "dt/dt_spi_device.h"  // Generated
#include "dt/dt_spi_host.h"    // Generated
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "i2c_regs.h"         // Generated
#include "spi_device_regs.h"  // Generated
#include "spi_host_regs.h"    // Generated

OTTF_DEFINE_TEST_CONFIG();

/**
 *  RSTMGR SW_RST_CTRL Test
 *
 *  This test checks RSTMGR.SW_RST_CTRL_N[index] with peripheral devices.
 *
 *  On Earlgrey, the RSTMGR.SW_RST_CTRL_N register has 8 bits. One of these
 *  controls USB_AON which has no software writeable CSRs, so it is not
 *  amenable to this test yet it is still reset with the expectation that
 *  it has no side-effects. The various bits control peripheral resets as
 *  follows:
 *
 * // index | device     |  test register |  reset value |  prgm value |
 * // ------------------------------------------------------------------
 * // 0     | SPI_DEVICE |  CFG           |  0x7f00      |  0x3f0c
 * // 1     | SPI_HOST0  |  CONFIGOPTS    |  0x0         |  0x3210000
 * // 2     | SPI_HOST1  |  CONFIGOPTS    |  0x0         |  0x6540000
 * // 3     | USB        |  EP_OUT_ENABLE |  0x0         |  0xc3
 * // 4     | USB_AON    |                |              |
 * // 5     | I2C0       |  TIMING0       |  0x0         |  0x8b00cfe
 * // 6     | I2C1       |  TIMING1       |  0x0         |  0x114010d8
 * // 7     | I2C2       |  TIMING2       |  0x0         |  0x19ec1595
 *
 * On Darjeeling, there are only 3 bits:
 *
 * // index | device     |  test register |  reset value |  prgm value |
 * // ------------------------------------------------------------------
 * // 0     | SPI_DEVICE |  CFG           |  0x7f00      |  0x3f0c
 * // 1     | SPI_HOST0  |  CONFIGOPTS    |  0x0         |  0x3210000
 * // 2     | I2C0       |  TIMING0       |  0x0         |  0x8b00cfe
 *
 * 'test register' is a rw type register under each peripheral device.
 * These registers are programmed with arbitrary values ('prgm value') before
 * resetting each peripheral, and the expectation is that when reset is
 * asserted the register value is set to its reset value. This test has
 * multiple rounds, one per peripheral.
 */

#define MAKE_INIT_FUNC(ip_)                                          \
  void ip_##_init(void *ip_, int32_t dt) {                           \
    CHECK_DIF_OK(dif##_##ip_##_init_from_dt((dt_##ip_##_t)dt, ip_)); \
  }

#define MAKE_BASE_ADDR_FUNC(ip_)                                    \
  uintptr_t ip_##_base_addr(int32_t dt, int32_t reg_block) {        \
    return dt_##ip_##_reg_block((dt_##ip_##_t)dt,                   \
                                (dt_##ip_##_reg_block_t)reg_block); \
  }

#define MAKE_RSTMGR_RESET_FUNC(ip_)                                 \
  dt_reset_t ip_##_rstmgr_reset(int32_t dt, int32_t device_reset) { \
    return dt_##ip_##_reset((dt_##ip_##_t)dt,                       \
                            (dt_##ip_##_reset_t)device_reset);      \
  }

#define MAKE_TEST_FUNCS(ip_) \
  MAKE_INIT_FUNC(ip_);       \
  MAKE_BASE_ADDR_FUNC(ip_);  \
  MAKE_RSTMGR_RESET_FUNC(ip_);

#if defined(OT_HAS_USBDEV)
MAKE_TEST_FUNCS(usbdev);
#endif  // defined(OT_HAS_USBDEV)

MAKE_TEST_FUNCS(spi_device);
MAKE_TEST_FUNCS(spi_host);
MAKE_TEST_FUNCS(i2c);

static void spi_device_config(void *dif) {
  uintptr_t handle_address =
      ((uintptr_t)dif - offsetof(dif_spi_device_handle_t, dev));
  dif_spi_device_handle_t *handle = (dif_spi_device_handle_t *)handle_address;
  dif_spi_device_config_t cfg = {
      .tx_order = kDifSpiDeviceBitOrderLsbToMsb,
      .rx_order = kDifSpiDeviceBitOrderLsbToMsb,
      .device_mode = kDifSpiDeviceModeDisabled,
  };
  CHECK_DIF_OK(dif_spi_device_configure(handle, cfg));
}

static void spi_host0_config(void *dif) {
  dif_spi_host_config_t cfg = {
      .spi_clock = 500000,
      .peripheral_clock_freq_hz = 1000000,
      .chip_select =
          {
              .idle = 1,
              .trail = 2,
              .lead = 3,
          },
      .full_cycle = false,
      .cpha = false,
      .cpol = false,
  };
  CHECK_DIF_OK(dif_spi_host_configure(dif, cfg));
}

#if defined(OPENTITAN_IS_EARLGREY)
static void spi_host1_config(void *dif) {
  dif_spi_host_config_t cfg = {
      .spi_clock = 2500000,
      .peripheral_clock_freq_hz = 5000000,
      .chip_select =
          {
              .idle = 4,
              .trail = 5,
              .lead = 6,
          },
      .full_cycle = false,
      .cpha = false,
      .cpol = false,
  };
  CHECK_DIF_OK(dif_spi_host_configure(dif, cfg));
}
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling only has 1 SPI Host
#else
#error "rstmgr_sw_rst_ctrl_test does not support this top"
#endif

static void i2c0_config(void *dif) {
  dif_i2c_config_t cfg = {
      .scl_time_high_cycles = 3326,
      .scl_time_low_cycles = 2224,
  };
  CHECK_DIF_OK(dif_i2c_configure(dif, cfg));
}

#if defined(OPENTITAN_IS_EARLGREY)
static void i2c1_config(void *dif) {
  dif_i2c_config_t cfg = {
      .rise_cycles = 4312,
      .fall_cycles = 4416,
  };
  CHECK_DIF_OK(dif_i2c_configure(dif, cfg));
}

static void i2c2_config(void *dif) {
  dif_i2c_config_t cfg = {
      .start_signal_setup_cycles = 5525,
      .start_signal_hold_cycles = 6636,
  };
  CHECK_DIF_OK(dif_i2c_configure(dif, cfg));
}
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling only has 1 I2C Controller
#else
#error "rstmgr_sw_rst_ctrl_test does not support this top"
#endif

static dif_spi_device_handle_t spi_dev;
static dif_spi_host_t spi_host0;
static dif_i2c_t i2c0;

#if defined(OPENTITAN_IS_EARLGREY)
static dif_spi_host_t spi_host1;
static dif_usbdev_t usbdev;
static dif_i2c_t i2c1;
static dif_i2c_t i2c2;
#elif defined(OPENTITAN_IS_DARJEELING)
/* Darjeeling does not have a USB device, and only has 1 I2C Controller and
SPI Host. */
#else
#error "rstmgr_sw_rst_ctrl_test does not support this top"
#endif

typedef struct test {
  /**
   * Name of the peripheral.
   */
  const char *name;
  /**
   * Initialization for the base address of the peripheral.
   *
   * Cannot be `NULL`.
   */
  uintptr_t (*get_base_address)(int32_t dt, int32_t reg_block);
  /*
   * The devicetable instance of the peripheral.
   */
  int32_t dt;
  /**
   * The register block that the test register belongs to.
   */
  int32_t reg_block;
  /**
   * Offset to the peripheral's test register.
   */
  ptrdiff_t offset;
  /**
   * Handle to the DIF object for this peripheral.
   */
  void *dif;
  /**
   * Initialization for the DIF based on an address location.
   *
   * May be `NULL`.
   */
  void (*init)(void *dif, int32_t dt);
  /**
   * Configuration and initialization actions for the device. This
   * will be passed the value of `dif` above.
   *
   * If `NULL`, the test register will be set to 'reset_vals[]'.
   */
  void (*config)(void *dif);
  /**
   * Arbitrary test register value before reset.
   */
  uint32_t program_val;
  /**
   * The device-local DT reset index for this device. By using the
   * corresponding dt instance, this is used to retrieve the correct
   * index in the reset manager for this device.
   */
  int32_t reset_index;
  /**
   * The DT function for getting the reset manager index of the
   * corresponding device for this test using the reset index.
   *
   * Cannot be `NULL`.
   */
  dt_reset_t (*get_rstmgr_rst_index)(int32_t dt, int32_t reset_index);
} test_t;

static const test_t kPeripherals[] = {
    {
        .name = "SPI_DEVICE",
        .get_base_address = spi_device_base_addr,
        .dt = (dt_spi_device_t)0,
        .reg_block = kDtSpiDeviceRegBlockCore,
        .offset = SPI_DEVICE_CFG_REG_OFFSET,
        .dif = &spi_dev.dev,
        .init = spi_device_init,
        .config = spi_device_config,
        .program_val = 0x3f0c,
        .reset_index = kDtSpiDeviceResetRst,
        .get_rstmgr_rst_index = spi_device_rstmgr_reset,
    },
    {
        .name = "SPI_HOST0",
        .get_base_address = spi_host_base_addr,
        .dt = (dt_spi_host_t)0,
        .reg_block = kDtSpiHostRegBlockCore,
        .offset = SPI_HOST_CONFIGOPTS_REG_OFFSET,
        .dif = &spi_host0,
        .init = spi_host_init,
        .config = spi_host0_config,
        .program_val = 0x3210000,
        .reset_index = kDtSpiHostResetRst,
        .get_rstmgr_rst_index = spi_host_rstmgr_reset,
    },
#if defined(OPENTITAN_IS_EARLGREY)
    {
        .name = "SPI_HOST1",
        .get_base_address = spi_host_base_addr,
        .dt = (dt_spi_host_t)1,
        .reg_block = kDtSpiHostRegBlockCore,
        .offset = SPI_HOST_CONFIGOPTS_REG_OFFSET,
        .dif = &spi_host1,
        .init = spi_host_init,
        .config = spi_host1_config,
        .program_val = 0x6540000,
        .reset_index = kDtSpiHostResetRst,
        .get_rstmgr_rst_index = spi_host_rstmgr_reset,
    },
    {
        .name = "USB",
        .get_base_address = usbdev_base_addr,
        .dt = (dt_usbdev_t)0,
        .reg_block = kDtUsbdevRegBlockCore,
        .offset = USBDEV_EP_OUT_ENABLE_REG_OFFSET,
        .dif = &usbdev,
        .init = usbdev_init,
        .program_val = 0xc3,
        .reset_index = kDtUsbdevResetRst,
        .get_rstmgr_rst_index = usbdev_rstmgr_reset,
    },
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling does not have a USB Device, and only has 1 SPI Host
#else
#error "rstmgr_sw_rst_ctrl_test does not support this top"
#endif
    {
        .name = "I2C0",
        .get_base_address = i2c_base_addr,
        .reg_block = kDtI2cRegBlockCore,
        .dt = (dt_i2c_t)0,
        .offset = I2C_TIMING0_REG_OFFSET,
        .dif = &i2c0,
        .init = i2c_init,
        .config = i2c0_config,
        .program_val = 0x8b00cfe,
        .reset_index = kDtI2cResetRst,
        .get_rstmgr_rst_index = i2c_rstmgr_reset,
    },
#if defined(OPENTITAN_IS_EARLGREY)
    {
        .name = "I2C1",
        .get_base_address = i2c_base_addr,
        .dt = (dt_i2c_t)1,
        .reg_block = kDtI2cRegBlockCore,
        .offset = I2C_TIMING1_REG_OFFSET,
        .dif = &i2c1,
        .init = i2c_init,
        .config = i2c1_config,
        .program_val = 0x114010d8,
        .reset_index = kDtI2cResetRst,
        .get_rstmgr_rst_index = i2c_rstmgr_reset,
    },
    {
        .name = "I2C2",
        .get_base_address = i2c_base_addr,
        .dt = (dt_i2c_t)2,
        .reg_block = kDtI2cRegBlockCore,
        .offset = I2C_TIMING2_REG_OFFSET,
        .dif = &i2c2,
        .init = i2c_init,
        .config = i2c2_config,
        .program_val = 0x19ec1595,
        .reset_index = kDtI2cResetRst,
        .get_rstmgr_rst_index = i2c_rstmgr_reset,
    },
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling only has 1 I2C Controller
#else
#error "rstmgr_sw_rst_ctrl_test does not support this top"
#endif
};

/**
 * Reads the value of the test register in a particular device.
 */
static uint32_t read_test_reg(const test_t *test) {
  uintptr_t base = test->get_base_address(test->dt, test->reg_block);
  return mmio_region_read32(mmio_region_from_addr(base), test->offset);
}

bool test_main(void) {
  dif_rstmgr_t rstmgr;
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kDtRstmgrAon, &rstmgr));

#if defined(OT_HAS_USBDEV)
  // For completeness reset USB_AON first, expecting no side-effects. The lame
  // check is that the rest of the test goes through with no problem.
  dt_reset_t reset = dt_usbdev_reset((dt_usbdev_t)0, kDtUsbdevResetRst);
  size_t sw_reset_index;
  CHECK_DIF_OK(
      dif_rstmgr_get_sw_reset_index(kDtRstmgrAon, reset, &sw_reset_index));
  CHECK_DIF_OK(dif_rstmgr_software_reset(&rstmgr, sw_reset_index,
                                         kDifRstmgrSoftwareReset));
#endif  // defined(OT_HAS_USBDEV)

  uint32_t reset_vals[ARRAYSIZE(kPeripherals)];
  for (size_t i = 0; i < ARRAYSIZE(kPeripherals); ++i) {
    if (kPeripherals[i].init != NULL) {
      kPeripherals[i].init(kPeripherals[i].dif, kPeripherals[i].dt);
    }
    reset_vals[i] = read_test_reg(&kPeripherals[i]);
    LOG_INFO("reset_val for %s is 0x%08x", kPeripherals[i].name, reset_vals[i]);
  }

  for (size_t i = 0; i < ARRAYSIZE(kPeripherals); ++i) {
    if (kPeripherals[i].config != NULL) {
      kPeripherals[i].config(kPeripherals[i].dif);
    } else {
      uintptr_t base = kPeripherals[i].get_base_address(
          kPeripherals[i].dt, kPeripherals[i].reg_block);
      mmio_region_write32(mmio_region_from_addr(base), kPeripherals[i].offset,
                          kPeripherals[i].program_val);
    }

    // add read back to make sure
    // all register access complete
    uint32_t got = read_test_reg(&kPeripherals[i]);
    LOG_INFO("programmed value : 0x%x", got);
  }

  for (size_t i = 0; i < ARRAYSIZE(kPeripherals); ++i) {
    dt_reset_t reset_index = kPeripherals[i].get_rstmgr_rst_index(
        kPeripherals[i].dt, kPeripherals[i].reset_index);
    size_t sw_reset_index;
    CHECK_DIF_OK(dif_rstmgr_get_sw_reset_index(kDtRstmgrAon, reset_index,
                                               &sw_reset_index));
    CHECK_DIF_OK(dif_rstmgr_software_reset(&rstmgr, sw_reset_index,
                                           kDifRstmgrSoftwareReset));

    uint32_t got = read_test_reg(&kPeripherals[i]);
    CHECK(got == reset_vals[i],
          "after configure: reset_val for %s mismatch: want 0x%x, got 0x%x",
          kPeripherals[i].name, reset_vals[i], got);
  }

  return true;
}
