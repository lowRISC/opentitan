// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"
#include "spi_device_regs.h"
#include "spi_host_regs.h"
#include "usbdev_regs.h"

/**
 *  RSTMGR SW_RST_CTRL Test
 *
 *  This test checks RSTMGR.SW_RST_CTRL_N[index] with peripheral devices.
 *  There are 8 RSTMGR.SW_RST_CTRL_N registers and each register
 *  controls peripheral reset as follows:
 *
 * // index | device     |  test register |  reset value |  prgm value |
 * // ------------------------------------------------------------------
 * // 0     | SPI_DEVICE |  CFG           |  0x7f00      |  0x3f0c
 * // 1     | SPI_HOST0  |  CONFIGOPTS    |  0x0         |  0x3210000
 * // 2     | SPI_HOST1  |  CONFIGOPTS    |  0x0         |  0x6540000
 * // 3     | USB        |  EP_OUT_ENABLE |  0x0         |  0xc3
 * // 4     | USBIF      |  RXENABLE_OUT  |  0x0         |  0x695
 * // 5     | I2C0       |  TIMING0       |  0x0         |  0x8b00cfe
 * // 6     | I2C1       |  TIMING1       |  0x0         |  0x114010d8
 * // 7     | I2C2       |  TIMING2       |  0x0         |  0x19ec1595
 *
 * 'test register' is a rw type register under each peripheral device.
 * During the test, these registers are programmed with arbitrary values. ('prgm
 * value') when sw resets are asserted, those values are updated to reset value.
 * In each round, the rstmgr asserts reset to each peripheral device and
 * each test register value is compared with the expected reset value.
 */

typedef struct node node_t;
typedef void config_f(node_t *);

// peripheral device template
// name : device name
// base : base address
// offset : offset to the test register
// handler : dif handler for each peripheral device
// config_f : function ptr to each peripheral program
// reset_val : reset value for comparison
// prgm_val : expected value for test register after configuration
//            function is called.
struct node {
  const char *name;
  uintptr_t base;
  ptrdiff_t offset;
  void *handler;
  config_f *config;
  uint32_t reset_val;
  uint32_t prgm_val;
};

// handler declaration
static dif_rstmgr_t rstmgr;
static dif_spi_device_t spi_dev;
static dif_spi_host_t spi_host0, spi_host1;
static dif_usbdev_t usbdev;
static dif_i2c_t i2c0, i2c1, i2c2;

#define kNumNodes kTopEarlgreyResetManagerSwResetsLast + 1
// pre declaration of template
static node_t test_node[kNumNodes];

// test register read from a given peripheral device
static uint32_t read_test_reg(node_t *node) {
  return (mmio_region_read32(mmio_region_from_addr(node->base), node->offset));
}

// init function
static void init_nodes(void) {
#define INITIALIZE(module_, index_)                                          \
  CHECK_DIF_OK(                                                              \
      dif_##module_##_init(mmio_region_from_addr(test_node[index_].base),    \
                           (dif_##module_##_t *)test_node[index_].handler)); \
  test_node[index_].reset_val = read_test_reg(&test_node[index_]);           \
  LOG_INFO("%s reset value=0x%x", test_node[index_].name,                    \
           test_node[index_].reset_val)

  INITIALIZE(spi_device, kTopEarlgreyResetManagerSwResetsSpiDevice);
  INITIALIZE(spi_host, kTopEarlgreyResetManagerSwResetsSpiHost0);
  INITIALIZE(spi_host, kTopEarlgreyResetManagerSwResetsSpiHost1);
  INITIALIZE(usbdev, kTopEarlgreyResetManagerSwResetsUsb);
  // USBIF INIT is covered by USB init
  INITIALIZE(i2c, kTopEarlgreyResetManagerSwResetsI2c0);
  INITIALIZE(i2c, kTopEarlgreyResetManagerSwResetsI2c1);
  INITIALIZE(i2c, kTopEarlgreyResetManagerSwResetsI2c2);
#undef INITIALIZE
}

// configuration function wrapper
static void spi_dev_config(node_t *node) {
  const uint16_t kFifoLen = 0x800;
  const dif_spi_device_config_t cfg = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderLsbToMsb,  // 1
      .rx_order = kDifSpiDeviceBitOrderLsbToMsb,  // 1
      .rx_fifo_timeout = 63,
      .rx_fifo_len = kFifoLen,
      .tx_fifo_len = kFifoLen,
  };
  CHECK_DIF_OK(dif_spi_device_configure(node->handler, &cfg));
  LOG_INFO("%s update value=0x%x", node->name, read_test_reg(node));
}
static void spi_host0_config(node_t *node) {
  const dif_spi_host_config_t cfg = {
      .spi_clock = 1000000,
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
  CHECK_DIF_OK(dif_spi_host_configure(node->handler, cfg));
  LOG_INFO("%s update value=0x%x", node->name, read_test_reg(node));
}
static void spi_host1_config(node_t *node) {
  const dif_spi_host_config_t cfg = {
      .spi_clock = 5000000,
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
  CHECK_DIF_OK(dif_spi_host_configure(node->handler, cfg));
  LOG_INFO("%s update value=0x%x", node->name, read_test_reg(node));
}
static void usbdev_config(node_t *node) {
  struct dif_usbdev_prop_config {
    uint32_t val;
  };
  const struct dif_usbdev_prop_config cfg = {
      .val = 195,  // 0xC3
  };
  mmio_region_write32(mmio_region_from_addr(node->base), node->offset, cfg.val);
  LOG_INFO("%s update value=0x%x", node->name, read_test_reg(node));
}
static void usbif_config(node_t *node) {
  struct dif_usbif_config {
    // only 12 bits
    uint32_t val;
  };
  const struct dif_usbif_config cfg = {
      .val = 1685,  // 0x695
  };
  mmio_region_write32(mmio_region_from_addr(node->base), node->offset, cfg.val);
  LOG_INFO("%s update value=0x%x", node->name, read_test_reg(node));
}
static void i2c0_config(node_t *node) {
  const dif_i2c_config_t cfg = {
      .scl_time_high_cycles = 3326,
      .scl_time_low_cycles = 2224,
  };
  CHECK_DIF_OK(dif_i2c_configure(node->handler, cfg));
  LOG_INFO("%s update value=0x%x", node->name, read_test_reg(node));
}
static void i2c1_config(node_t *node) {
  const dif_i2c_config_t cfg = {
      .rise_cycles = 4312,
      .fall_cycles = 4416,
  };
  CHECK_DIF_OK(dif_i2c_configure(node->handler, cfg));
  LOG_INFO("%s update value=0x%x", node->name, read_test_reg(node));
}
static void i2c2_config(node_t *node) {
  const dif_i2c_config_t cfg = {
      .start_signal_setup_cycles = 5525,
      .start_signal_hold_cycles = 6636,
  };
  CHECK_DIF_OK(dif_i2c_configure(node->handler, cfg));
  LOG_INFO("%s update value=0x%x", node->name, read_test_reg(node));
}

// peripheral template
static node_t test_node[kNumNodes] = {
    [kTopEarlgreyResetManagerSwResetsSpiDevice] =
        {
            .name = "SPI_DEVICE",
            .base = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
            .offset = SPI_DEVICE_CFG_REG_OFFSET,
            .handler = &spi_dev,
            .config = spi_dev_config,
            .prgm_val = 0x3f0c,
        },
    [kTopEarlgreyResetManagerSwResetsSpiHost0] =
        {
            .name = "SPI_HOST0",
            .base = TOP_EARLGREY_SPI_HOST0_BASE_ADDR,
            .offset = SPI_HOST_CONFIGOPTS_REG_OFFSET,
            .handler = &spi_host0,
            .config = spi_host0_config,
            .prgm_val = 0x3210000,
        },
    [kTopEarlgreyResetManagerSwResetsSpiHost1] =
        {
            .name = "SPI_HOST1",
            .base = TOP_EARLGREY_SPI_HOST1_BASE_ADDR,
            .offset = SPI_HOST_CONFIGOPTS_REG_OFFSET,
            .handler = &spi_host1,
            .config = spi_host1_config,
            .prgm_val = 0x6540000,
        },
    [kTopEarlgreyResetManagerSwResetsUsb] =
        {
            .name = "USB",
            .base = TOP_EARLGREY_USBDEV_BASE_ADDR,
            .offset = USBDEV_EP_OUT_ENABLE_REG_OFFSET,
            .handler = &usbdev,
            .config = usbdev_config,
            .prgm_val = 0xc3,
        },
    [kTopEarlgreyResetManagerSwResetsUsbif] =
        {
            .name = "USBIF",
            .base = TOP_EARLGREY_USBDEV_BASE_ADDR,
            .offset = USBDEV_RXENABLE_OUT_REG_OFFSET,
            .config = usbif_config,
            .prgm_val = 0x695,
        },
    [kTopEarlgreyResetManagerSwResetsI2c0] =
        {
            .name = "I2C0",
            .base = TOP_EARLGREY_I2C0_BASE_ADDR,
            .offset = I2C_TIMING0_REG_OFFSET,
            .handler = &i2c0,
            .config = i2c0_config,
            .prgm_val = 0x8b00cfe,
        },
    [kTopEarlgreyResetManagerSwResetsI2c1] =
        {
            .name = "I2C1",
            .base = TOP_EARLGREY_I2C1_BASE_ADDR,
            .offset = I2C_TIMING1_REG_OFFSET,
            .handler = &i2c1,
            .config = i2c1_config,
            .prgm_val = 0x114010d8,
        },
    [kTopEarlgreyResetManagerSwResetsI2c2] =
        {
            .name = "I2C2",
            .base = TOP_EARLGREY_I2C2_BASE_ADDR,
            .offset = I2C_TIMING2_REG_OFFSET,
            .handler = &i2c2,
            .config = i2c2_config,
            .prgm_val = 0x19ec1595,
        },
};

bool test_main(void) {
  // initialize reset manager

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // reset all devices
  init_nodes();

  // program test reigster in each device
  for (int n = kTopEarlgreyResetManagerSwResetsSpiDevice; n < kNumNodes; ++n) {
    test_node[n].config(&test_node[n]);
    uint32_t obs_val = read_test_reg(&test_node[n]);
    CHECK(obs_val == test_node[n].prgm_val,
          "after configure: %s obs != exp : 0x%x != 0x%x", test_node[n].name,
          obs_val, test_node[n].prgm_val);
  }

  // reset one at a time and check
  for (int n = kTopEarlgreyResetManagerSwResetsSpiDevice; n < kNumNodes; ++n) {
    CHECK_DIF_OK(
        dif_rstmgr_software_reset(&rstmgr, n, kDifRstmgrSoftwareReset));

    uint32_t obs_val = read_test_reg(&test_node[n]);
    CHECK(obs_val == test_node[n].reset_val,
          "final: %s obs != exp : 0x%x != 0x%x", test_node[n].name, obs_val,
          test_node[n].reset_val);
  }

  return true;
}
