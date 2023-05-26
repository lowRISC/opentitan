// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

enum {

  kHart = kTopEarlgreyPlicTargetIbex0,

  kDeviceAddr = 0x22,
  // Registers
  kSwResetReg = 0xDF,
  kManufacturerIdReg = 0xDE,
  kProductIdReg = 0xDD,
  kRxDelayReg = 0xDC,
  kTxDelayReg = 0xDB,
  kCache63BitsReg = 0xCF,
  // Registers values
  kManufacturerId = 0xA1,
  kProductId = 0xA2,

  // Others
  kDefaultTimeoutMicros = 10000,
};

/**
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
// Hold the irs result.
static volatile status_t isr_result;
// Used to sync the irs and the main thread.
static volatile dif_i2c_irq_t irq_fired;
static dif_rv_plic_t plic;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

/**
 * Provides external IRQ handling for this test.
 *
 * This function overrides the default OTTF external ISR.
 *
 * For each IRQ, it performs the following:
 * 1. Claims the IRQ fired (finds PLIC IRQ index).
 * 2. Checks that the index belongs to the expected peripheral.
 * 3. Checks that only the correct / expected IRQ is triggered.
 * 4. Clears the IRQ at the peripheral.
 * 5. Completes the IRQ service at PLIC.
 */
static status_t external_isr(void) {
  dif_rv_plic_irq_id_t plic_irq_id;
  TRY(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  TRY_CHECK(peripheral == kTopEarlgreyPlicPeripheralI2c0,
            "IRQ from incorrect peripheral: exp = %d(i2c0), found = %d",
            kTopEarlgreyPlicPeripheralI2c0, peripheral);

  irq_fired =
      (dif_i2c_irq_t)(plic_irq_id - (dif_rv_plic_irq_id_t)
                                        kTopEarlgreyPlicIrqIdI2c0FmtThreshold);

  LOG_INFO("%s: plic:%d, i2c:%d", __func__, plic_irq_id, irq_fired);
  TRY(dif_i2c_irq_acknowledge(&i2c, irq_fired));

  // Complete the IRQ at PLIC.
  TRY(dif_rv_plic_irq_complete(&plic, kHart, plic_irq_id));
  return OK_STATUS();
}

void ottf_external_isr(void) {
  status_t tmp = external_isr();
  if (status_ok(isr_result)) {
    isr_result = tmp;
  }
}

// We make this a macro to show the caller line number when printing a error.
#define CHECK_IRQ_EQ(irq)                                                \
  do {                                                                   \
    irq_global_ctrl(false);                                              \
    if (irq_fired == UINT32_MAX) {                                       \
      wait_for_interrupt();                                              \
      irq_global_ctrl(true);                                             \
    }                                                                    \
    TRY_CHECK(irq_fired == irq, "Got %d, expected %d.", irq_fired, irq); \
  } while (false)

static status_t read_manufacture_id(void) {
  uint8_t reg = kManufacturerIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data, kDefaultTimeoutMicros));
  TRY_CHECK(data == kManufacturerId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t read_product_id(void) {
  uint8_t reg = kProductIdReg, data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, 1, &data, kDefaultTimeoutMicros));
  TRY_CHECK(data == kProductId, "Unexpected value %x", data);
  return OK_STATUS();
}

static status_t rx_stretch_timeout(void) {
  enum { kTimeoutMillis = 15 };
  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqStretchTimeout,
                              kDifToggleEnabled));

  // Set the delay that will make the target to stretch the clock.
  {
    uint8_t write_buffer[2] = {kRxDelayReg, kTimeoutMillis};
    TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_buffer),
                            write_buffer, true));
  }

  uint32_t cycles = (kTimeoutMillis - 1) * 100;
  TRY(dif_i2c_enable_clock_stretching_timeout(&i2c, kDifToggleEnabled, cycles));

  uint8_t reg = kProductIdReg;
  uint8_t data = 0;
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 1, &reg, true));

  irq_global_ctrl(false);
  irq_fired = UINT32_MAX;
  irq_global_ctrl(true);
  TRY(i2c_testutils_issue_read(&i2c, kDeviceAddr, 1));
  CHECK_IRQ_EQ(kDifI2cIrqStretchTimeout);

  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqStretchTimeout,
                              kDifToggleDisabled));

  // Reset the delay to disable clock stretching.
  {
    uint8_t write_buffer[2] = {kRxDelayReg, 0};
    TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_buffer),
                            write_buffer, true));

    TRY(dif_i2c_reset_rx_fifo(&i2c));
  }

  TRY(dif_i2c_reset_rx_fifo(&i2c));

  return OK_STATUS();
}

static status_t tx_stretch(void) {
  enum { kTimeoutMillis = 1, kTxSize = 63 };

  // Set the delay that will make the target to stretch the clock.
  {
    uint8_t write_buffer[2] = {kTxDelayReg, kTimeoutMillis};
    TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_buffer),
                            write_buffer, true));
  }

  // Init buffer with random data.
  uint8_t rnd_data[kTxSize];
  for (int i = 0; i < sizeof(rnd_data); ++i) {
    uint32_t rand;
    TRY(rv_core_ibex_testutils_get_rnd_data(&rv_core_ibex, 1000, &rand));
    rnd_data[i] = rand & 0xFF;
  }
  uint8_t write_buffer[kTxSize + 1];
  write_buffer[0] = kCache63BitsReg;
  memcpy(&write_buffer[1], rnd_data, sizeof(rnd_data));
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_buffer), write_buffer,
                          false));
  // The transmission may take a long time due to the clock stretching.
  const size_t timeout = (kTimeoutMillis * kTxSize) * 1000;
  busy_spin_micros(timeout);

  uint8_t reg = kCache63BitsReg;
  uint8_t read_data[kTxSize] = {0};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(reg), &reg, true));
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(read_data), read_data,
                         timeout));
  TRY_CHECK_ARRAYS_EQ(read_data, rnd_data, sizeof(read_data));

  // Reset the delay to disable clock stretching.
  {
    uint8_t write_buffer[2] = {kTxDelayReg, 0};
    TRY(i2c_testutils_write(&i2c, kDeviceAddr, sizeof(write_buffer),
                            write_buffer, true));
  }

  return OK_STATUS();
}

static status_t test_init(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);

  TRY(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux));
  TRY(i2c_testutils_connect_i2c_to_pinmux_pins(&pinmux, 0));
  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  TRY(dif_rv_plic_init(base_addr, &plic));

  rv_plic_testutils_irq_range_enable(&plic, kHart,
                                     kTopEarlgreyPlicIrqIdI2c0FmtThreshold,
                                     kTopEarlgreyPlicIrqIdI2c0HostTimeout);

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(test_init());

  dif_i2c_speed_t speeds[] = {kDifI2cSpeedStandard, kDifI2cSpeedFast,
                              kDifI2cSpeedFastPlus};

  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(speeds); ++i) {
    CHECK_STATUS_OK(i2c_testutils_set_speed(&i2c, speeds[i]));
    EXECUTE_TEST(test_result, read_manufacture_id);
    EXECUTE_TEST(test_result, read_product_id);
    EXECUTE_TEST(test_result, rx_stretch_timeout);
    EXECUTE_TEST(test_result, tx_stretch);
  }

  return status_ok(test_result) && status_ok(isr_result);
}
