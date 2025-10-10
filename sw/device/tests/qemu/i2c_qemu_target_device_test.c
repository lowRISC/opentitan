// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

/*
 * This test emulates a simple memory device over Opentitan's I2C target mode.
 * The device consists of a 256-byte memory that can be written and read.
 *
 * On a write transfer to the device, the first byte written sets the pointer
 * to which subsequent bytes are written to and read from.
 * Subsequent written bytes set the value in memory at the pointer's location
 * and increment it. Reads from the device read from the memory at the
 * pointer's location and increment it.
 *
 * This test runs in QEMU. Read and write transfers should be performed with
 * Opentitantool.
 */

enum {
  kHart = kTopEarlgreyPlicTargetIbex0,
  /* Our address on the I2C bus for target mode. */
  kI2cDeviceTargetAddr = 0x40,
  /* Our address mask for I2C target mode: All 1s for exact match */
  kI2CDeviceTargetMask = 0x7f,
  /* TX level threshold and how much to fill to */
  kTxThreshold = 4u,
  kTxFill = 2 * kTxThreshold,
};

static dif_i2c_t i2c;
static dif_rv_plic_t plic;

/* Memory device that Opentitan will be emulating in I2C Target Mode */
static struct {
  uint8_t data[256];
  uint8_t ptr;
  bool first_byte;
} device;

/* Fill TX FIFO with memory data */
status_t i2c_eeprom_tx_fill(void) {
  dif_i2c_level_t tx_lvl;
  do {
    TRY(dif_i2c_transmit_byte(&i2c, device.data[device.ptr++]));
    TRY(dif_i2c_get_fifo_levels(&i2c, NULL, NULL, &tx_lvl, NULL));
  } while (tx_lvl < kTxFill);
  return OK_STATUS();
}

/* Handle I2C state change and data write */
status_t i2c_eeprom_process_byte(uint8_t data, dif_i2c_signal_t signal) {
  switch (signal) {
    case kDifI2cSignalStart:
      device.first_byte = true;
      if ((data & 1) == 1) {
        /* is a read command, enable tx threshold interrupts and queue
         * response bytes, reading from the memory */
        TRY(dif_i2c_reset_tx_fifo(&i2c));
        TRY(i2c_eeprom_tx_fill());
        TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqTxThreshold,
                                    kDifToggleEnabled));
      }
      break;
    case kDifI2cSignalStop:
      TRY(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqTxThreshold,
                                  kDifToggleDisabled));
      TRY(dif_i2c_reset_tx_fifo(&i2c));
      break;
    case kDifI2cSignalNone:
      /* Only received during an ongoing write transaction, so this is a write
       * command */
      if (device.first_byte) {
        device.first_byte = false;
        device.ptr = data;
      } else {
        device.data[device.ptr++] = data;
      }
      break;

    default:
      return ABORTED();
  }
  return OK_STATUS();
}

status_t i2c_eeprom_acq_bytes(void) {
  dif_i2c_status_t status;
  do {
    uint8_t acq_byte = 0;
    dif_i2c_signal_t signal = kDifI2cSignalNone;
    TRY(dif_i2c_acquire_byte(&i2c, &acq_byte, &signal));
    TRY(i2c_eeprom_process_byte(acq_byte, signal));
    TRY(dif_i2c_get_status(&i2c, &status));
  } while (!status.acq_fifo_empty);
  return OK_STATUS();
}

status_t i2c_emulate_eeprom(dif_i2c_irq_t irq) {
  if (irq == kDifI2cIrqAcqThreshold) {
    TRY(i2c_eeprom_acq_bytes());
  } else if (irq == kDifI2cIrqTxThreshold) {
    TRY(i2c_eeprom_tx_fill());
  } else {
    return ABORTED();
  }
  return OK_STATUS();
}

static status_t i2c_setup(dif_i2c_t *i2c) {
  dif_i2c_id_t i2c_address = {.address = kI2cDeviceTargetAddr,
                              .mask = kI2CDeviceTargetMask};
  TRY(dif_i2c_set_device_id(i2c, &i2c_address, NULL));
  TRY(dif_i2c_set_target_watermarks(i2c, kTxThreshold /* tx level */,
                                    0 /* acq_level */));
  TRY(dif_i2c_device_set_enabled(i2c, kDifToggleEnabled));
  return OK_STATUS();
}

static status_t external_isr(void) {
  dif_rv_plic_irq_id_t plic_irq_id;
  /* Claim IRQ */
  TRY(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));
  /* Check that it is for the I2C0 */
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  TRY_CHECK(peripheral == kTopEarlgreyPlicPeripheralI2c0);
  /* index into I2C0 IRQs */
  dif_i2c_irq_t irq_id =
      (dif_i2c_irq_t)(plic_irq_id - (dif_rv_plic_irq_id_t)
                                        kTopEarlgreyPlicIrqIdI2c0FmtThreshold);

  TRY(i2c_emulate_eeprom(irq_id));

  /* Acknowledge IRQ and return */
  TRY(dif_i2c_irq_acknowledge(&i2c, irq_id));
  TRY(dif_rv_plic_irq_complete(&plic, kHart, plic_irq_id));
  return OK_STATUS();
}

void ottf_external_isr(uint32_t *exc_info) {
  (void)exc_info;
  (void)external_isr();
}

bool test_main(void) {
  device.ptr = 0u;
  device.first_byte = true;
  memset(&device.data, 0u, ARRAYSIZE(device.data));

  mmio_region_t region;
  region = mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(region, &i2c));
  CHECK_STATUS_OK(i2c_setup(&i2c));

  region = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(region, &plic));
  rv_plic_testutils_irq_range_enable(&plic, kHart,
                                     kTopEarlgreyPlicIrqIdI2c0FmtThreshold,
                                     kTopEarlgreyPlicIrqIdI2c0HostTimeout);

  CHECK_DIF_OK(
      dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqAcqThreshold, kDifToggleEnabled));

  irq_global_ctrl(true);
  irq_external_ctrl(true);
  LOG_INFO("SYNC: Device Ready");

  while (true) {
    wait_for_interrupt();
  }

  return status_ok(OK_STATUS());
}
