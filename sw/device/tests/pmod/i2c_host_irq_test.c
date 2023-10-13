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

/**
 * This test uses an EEPROM device on the BoB to test the host IRQs.
 * The EEPROM was chosen because it easily allow to test the nak irq, since
 * every attempt to read an address will return nak as a way to signal it is
 * busy.
 */
enum {
  kHart = kTopEarlgreyPlicTargetIbex0,
  kIrqVoid = UINT32_MAX,
  kDeviceAddr = 0x52,

  // Default timeout for i2c reads.
  kDefaultTimeoutMicros = 5000,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_pinmux_t pinmux;
static dif_i2c_t i2c;
static dif_rv_plic_t plic;

// Hold the test result.
static volatile status_t isr_result;
// Used to sync the irs and the main thread.
static volatile dif_i2c_irq_t irq_fired;

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
  TRY_CHECK(peripheral == kTopEarlgreyPlicPeripheralI2c2,
            "IRQ from incorrect peripheral: exp = %d(i2c2), found = %d",
            kTopEarlgreyPlicPeripheralI2c2, peripheral);

  irq_fired =
      (dif_i2c_irq_t)(plic_irq_id - (dif_rv_plic_irq_id_t)
                                        kTopEarlgreyPlicIrqIdI2c2FmtThreshold);

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
    if (irq_fired == kIrqVoid) {                                         \
      wait_for_interrupt();                                              \
      irq_global_ctrl(true);                                             \
    }                                                                    \
    TRY_CHECK(irq_fired == irq, "Got %d, expected %d.", irq_fired, irq); \
  } while (false)

static status_t write_byte(const uint8_t addr[2], uint8_t byte) {
  uint8_t data[3] = {addr[0], addr[1], byte};
  return i2c_testutils_write(&i2c, kDeviceAddr, sizeof(data), data, false);
}

static status_t nak_irq(void) {
  // Clean any previous state.
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqNak));
  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqNak, kDifToggleEnabled));

  // Write a byte to some random address.
  const uint8_t kAddr[2] = {0x03, 0x21};
  TRY(write_byte(kAddr, 0xAB));

  irq_global_ctrl(false);
  irq_fired = kIrqVoid;
  irq_global_ctrl(true);

  // Wait for the write to finish.
  uint8_t dummy = 0;
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(dummy), &dummy, 1));
  CHECK_IRQ_EQ(kDifI2cIrqNak);

  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqNak, kDifToggleDisabled));
  return OK_STATUS();
}

static status_t nak_irq_disabled(void) {
  // Clean any previous state.
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqNak));
  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqNak, kDifToggleEnabled));

  // Write a byte to some random address to be read.
  const uint8_t kAddr[2] = {0x03, 0x21};
  TRY(write_byte(kAddr, 0xAB));

  irq_global_ctrl(false);
  irq_fired = kIrqVoid;
  irq_global_ctrl(true);

  dif_i2c_fmt_flags_t flags = {.start = true,
                               .stop = false,
                               .read = false,
                               .read_cont = false,
                               .suppress_nak_irq = true};

  // Address the device to read, which should return a NACK as it needs more
  // time to be read.
  TRY(dif_i2c_write_byte_raw(&i2c, kDeviceAddr << 1 | 0x01, flags));

  TRY(i2c_testutils_wait_transaction_finish(&i2c));
  TRY_CHECK(irq_fired != kDifI2cIrqNak, "Unexpected IRQ %u", irq_fired);

  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqNak, kDifToggleDisabled));
  return OK_STATUS();
}

static status_t cmd_complete_irq(void) {
  // Clean any previous state.
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqCmdComplete, kDifToggleEnabled));

  irq_global_ctrl(false);
  irq_fired = kIrqVoid;
  irq_global_ctrl(true);

  // Write a byte to some random address.
  const uint8_t kAddr[2] = {0x03, 0x21};
  TRY(write_byte(kAddr, 0xAB));

  CHECK_IRQ_EQ(kDifI2cIrqCmdComplete);

  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqCmdComplete, kDifToggleDisabled));
  return OK_STATUS();
}

static status_t fmt_threshold_irq(void) {
  // Clean any previous state.
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqFmtThreshold));
  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqFmtThreshold, kDifToggleEnabled));
  TRY(dif_i2c_set_watermarks(&i2c, /*rx_level=*/kDifI2cLevel30Byte,
                             /*fmt_level=*/kDifI2cLevel4Byte));

  irq_global_ctrl(false);
  irq_fired = kIrqVoid;
  irq_global_ctrl(true);

  const uint8_t kAddr[2] = {0x03, 0x21};
  // Put five transactions into the fifo and expects an IRQ when the fmt_fifo
  // level drops to four.
  for (size_t i = 0; i < 5; ++i) {
    TRY(write_byte(kAddr, 0xAB));
  }

  CHECK_IRQ_EQ(kDifI2cIrqFmtThreshold);

  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqFmtThreshold,
                              kDifToggleDisabled));
  return OK_STATUS();
}

static status_t fmt_overflow_irq(void) {
  // Clean any previous state.
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqFmtOverflow));
  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqFmtOverflow, kDifToggleEnabled));

  irq_global_ctrl(false);
  irq_fired = kIrqVoid;
  irq_global_ctrl(true);
  const uint8_t kAddr[2] = {0x03, 0x21};
  // Overwhelm the fmt_fifo to generate a Overflow IRQ.
  for (size_t i = 0; i < 20; ++i) {
    TRY(write_byte(kAddr, 0xAB));
  }

  CHECK_IRQ_EQ(kDifI2cIrqFmtOverflow);

  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqFmtOverflow, kDifToggleDisabled));
  return OK_STATUS();
}

static status_t rx_threshold_irq(void) {
  // Clean any previous state.
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqRxThreshold));
  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqRxThreshold, kDifToggleEnabled));
  TRY(dif_i2c_set_watermarks(&i2c, /*rx_level=*/kDifI2cLevel8Byte,
                             /*fmt_level=*/kDifI2cLevel4Byte));

  irq_global_ctrl(false);
  irq_fired = kIrqVoid;
  irq_global_ctrl(true);

  uint8_t bytes[16];
  const uint8_t kAddr[2] = {0x03, 0x21};
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 2, kAddr, true));
  // Try to read more than the watermark to trigger the IRQ.
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(bytes), bytes,
                         kDefaultTimeoutMicros));

  CHECK_IRQ_EQ(kDifI2cIrqRxThreshold);

  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqRxThreshold, kDifToggleDisabled));
  return OK_STATUS();
}

static status_t rx_overflow_irq(void) {
  // Clean any previous state.
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqRxOverflow));
  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqRxOverflow, kDifToggleEnabled));

  irq_global_ctrl(false);
  irq_fired = kIrqVoid;
  irq_global_ctrl(true);

  const uint8_t kAddr[2] = {0x03, 0x21};
  uint8_t bytes[I2C_PARAM_FIFO_DEPTH + 1];
  TRY(i2c_testutils_write(&i2c, kDeviceAddr, 2, kAddr, true));
  // Try to read more than the fifo depth to trigger the IRQ.
  TRY(i2c_testutils_read(&i2c, kDeviceAddr, sizeof(bytes), bytes,
                         kDefaultTimeoutMicros));

  CHECK_IRQ_EQ(kDifI2cIrqRxOverflow);

  TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqRxOverflow, kDifToggleDisabled));
  return OK_STATUS();
}

static status_t test_init(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);

  TRY(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux));

  TRY(i2c_testutils_select_pinmux(&pinmux, 2));

  TRY(dif_i2c_host_set_enabled(&i2c, kDifToggleEnabled));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  TRY(dif_rv_plic_init(base_addr, &plic));

  rv_plic_testutils_irq_range_enable(&plic, kHart,
                                     kTopEarlgreyPlicIrqIdI2c2FmtThreshold,
                                     kTopEarlgreyPlicIrqIdI2c2HostTimeout);

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  return OK_STATUS();
}

bool test_main(void) {
  status_t test_result;
  CHECK_STATUS_OK(test_init());

  test_result = OK_STATUS();
  CHECK_STATUS_OK(i2c_testutils_set_speed(&i2c, kDifI2cSpeedStandard));
  EXECUTE_TEST(test_result, nak_irq);
  EXECUTE_TEST(test_result, nak_irq_disabled);
  EXECUTE_TEST(test_result, cmd_complete_irq);
  EXECUTE_TEST(test_result, fmt_threshold_irq);
  EXECUTE_TEST(test_result, fmt_overflow_irq);
  EXECUTE_TEST(test_result, rx_threshold_irq);
  EXECUTE_TEST(test_result, rx_overflow_irq);

  return status_ok(test_result);
}
