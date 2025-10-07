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
 * We also listen for another address on the I2C bus. Writes to that address
 * are used to signal successful termination of the test with a magic value.
 *
 * This test runs in QEMU. Read and write transfers should be performed with
 * Opentitantool.
 */

enum {
  kHart = kTopEarlgreyPlicTargetIbex0,
  // Our address on the bus. On this address, emulates a memory device
  kI2cTargetMemoryDeviceAddr = 0x40u,
  // Second address for our device. Sending a magic value to this address causes
  // the test to terminate successfully.
  kI2cTargetMagicDeviceAddr = 0x41u,
  // Our address mask for I2C target mode: All 1s except least significant bit,
  // to match addresses 0x40 and 0x41
  kI2cTargetDeviceMask = 0x7eu,
  // TX level threshold and how much to fill to for device reads
  kTxThreshold = 4u,
  kTxFill = 2u * kTxThreshold,
  // Memory device memory size
  kMemorySize = 256u,
  // Magic number to terminate the test successfully
  kMagic = 0xaau,
};

static_assert(
    kMemorySize <= 256u,
    "Memory size must be at most the number of representable byte values");

static dif_i2c_t i2cs[3];
static dif_rv_plic_t plic;

// Memory device that Opentitan will be emulating in I2C Target Mode
struct device {
  /* Memory data */
  uint8_t data[kMemorySize];
  // Index into memory data, set by first write on byte and then
  // auto-incremented on read/write byte
  uint8_t ptr;
  // Whether the next byte is the first byte to set the memory pointer
  bool first_byte;
  // Target used for this transfer, used by the device to emulate different
  // functionality based on the address used
  uint8_t address;
};

static struct device devices[3];

static volatile bool quit;
static volatile status_t isr_status;

static status_t external_isr(void);

void ottf_external_isr(uint32_t *exc_info) {
  OT_DISCARD(exc_info);
  isr_status = external_isr();
}

// Fill TX FIFO with memory data
status_t i2c_mem_device_tx_fill(size_t i2c_idx) {
  dif_i2c_t *i2c = &i2cs[i2c_idx];
  struct device *device = &devices[i2c_idx];
  dif_i2c_level_t tx_lvl;
  do {
    TRY(dif_i2c_transmit_byte(i2c, device->data[device->ptr]));
    device->ptr = (device->ptr + 1) % kMemorySize;
    TRY(dif_i2c_get_fifo_levels(i2c, NULL, NULL, &tx_lvl, NULL));
  } while (tx_lvl < kTxFill);
  return OK_STATUS();
}

status_t i2c_mem_device_start(size_t i2c_idx, uint8_t data) {
  dif_i2c_t *i2c = &i2cs[i2c_idx];
  struct device *device = &devices[i2c_idx];
  device->first_byte = true;
  if ((data & 0x1u) == 1u) {
    // is a read command, enable tx threshold interrupts and queue
    // response bytes, reading from the memory
    TRY(dif_i2c_reset_tx_fifo(i2c));
    TRY(i2c_mem_device_tx_fill(i2c_idx));
    TRY(dif_i2c_set_target_watermarks(i2c, /*tx level=*/kTxThreshold,
                                      /* acq_level */ 0u));
    TRY(dif_i2c_irq_set_enabled(i2c, kDifI2cIrqTxThreshold, kDifToggleEnabled));
  }
  return OK_STATUS();
}

status_t i2c_mem_device_process_byte(size_t i2c_idx, uint8_t data) {
  struct device *device = &devices[i2c_idx];
  // Only received during an ongoing write transaction, so this is a write
  // command
  if (device->first_byte) {
    device->first_byte = false;
    device->ptr = data;
  } else {
    device->data[device->ptr] = data;
    device->ptr = (device->ptr + 1) % kMemorySize;
  }
  return OK_STATUS();
}

status_t i2c_mem_device_stop(size_t i2c_idx) {
  dif_i2c_t *i2c = &i2cs[i2c_idx];
  TRY(dif_i2c_irq_set_enabled(i2c, kDifI2cIrqTxThreshold, kDifToggleDisabled));
  TRY(dif_i2c_set_target_watermarks(i2c, /*tx level=*/0u,
                                    /* acq_level */ 0u));
  TRY(dif_i2c_reset_tx_fifo(i2c));
  return OK_STATUS();
}

// Handle I2C transaction state change and data write
status_t i2c_device_process_byte(size_t i2c_idx, uint8_t data,
                                 dif_i2c_signal_t signal) {
  struct device *device = &devices[i2c_idx];
  switch (signal) {
    case kDifI2cSignalStart:
      device->address = (data >> 1u);
      if (device->address == kI2cTargetMemoryDeviceAddr) {
        // emulate the memory device
        TRY(i2c_mem_device_start(i2c_idx, data));
      } else if (device->address != kI2cTargetMagicDeviceAddr) {
        // unreachable
        return ABORTED();
      }
      break;
    case kDifI2cSignalStop:
      if (device->address == kI2cTargetMemoryDeviceAddr) {
        // emulate the memory device
        TRY(i2c_mem_device_stop(i2c_idx));
      } else if (device->address != kI2cTargetMagicDeviceAddr) {
        // unreachable
        return ABORTED();
      }
      break;
    case kDifI2cSignalNone:
      if (device->address == kI2cTargetMemoryDeviceAddr) {
        TRY(i2c_mem_device_process_byte(i2c_idx, data));
      } else if (device->address == kI2cTargetMagicDeviceAddr) {
        // quit if magic value was written
        quit = (data == kMagic);
      } else {
        // unreachable
        return ABORTED();
      }
      break;
    default:
      return ABORTED();
  }
  return OK_STATUS();
}

status_t i2c_device_acq_bytes(size_t i2c_idx) {
  dif_i2c_t *i2c = &i2cs[i2c_idx];
  dif_i2c_status_t status;
  do {
    uint8_t acq_byte = 0u;
    dif_i2c_signal_t signal = kDifI2cSignalNone;
    TRY(dif_i2c_acquire_byte(i2c, &acq_byte, &signal));
    TRY(i2c_device_process_byte(i2c_idx, acq_byte, signal));
    TRY(dif_i2c_get_status(i2c, &status));
  } while (!status.acq_fifo_empty);
  return OK_STATUS();
}

status_t i2c_device_emulate(size_t i2c_idx, dif_i2c_irq_t irq) {
  if (irq == kDifI2cIrqAcqThreshold) {
    TRY(i2c_device_acq_bytes(i2c_idx));
  } else if (irq == kDifI2cIrqTxThreshold) {
    TRY(i2c_mem_device_tx_fill(i2c_idx));
  } else {
    // Unexpected IRQ
    return ABORTED();
  }
  return OK_STATUS();
}

static status_t i2c_setup(dif_i2c_t *i2c) {
  dif_i2c_id_t i2c_address = {.address = kI2cTargetMemoryDeviceAddr,
                              .mask = kI2cTargetDeviceMask};
  TRY(dif_i2c_set_device_id(i2c, &i2c_address, NULL));
  TRY(dif_i2c_set_target_watermarks(i2c, /*tx level=*/0u,
                                    /* acq_level */ 0u));
  TRY(dif_i2c_device_set_enabled(i2c, kDifToggleEnabled));
  return OK_STATUS();
}

static status_t external_isr(void) {
  dif_rv_plic_irq_id_t plic_irq_id;
  // Claim IRQ
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  size_t i2c_idx = 0;
  dif_i2c_irq_t i2c_irq_id = 0;
  switch (peripheral) {
    case kTopEarlgreyPlicPeripheralI2c0:
      i2c_idx = 0;
      i2c_irq_id = (dif_i2c_irq_t)(plic_irq_id -
                                   (dif_rv_plic_irq_id_t)
                                       kTopEarlgreyPlicIrqIdI2c0FmtThreshold);
      break;
    case kTopEarlgreyPlicPeripheralI2c1:
      i2c_idx = 1;
      i2c_irq_id = (dif_i2c_irq_t)(plic_irq_id -
                                   (dif_rv_plic_irq_id_t)
                                       kTopEarlgreyPlicIrqIdI2c1FmtThreshold);
      break;
    case kTopEarlgreyPlicPeripheralI2c2:
      i2c_idx = 2;
      i2c_irq_id = (dif_i2c_irq_t)(plic_irq_id -
                                   (dif_rv_plic_irq_id_t)
                                       kTopEarlgreyPlicIrqIdI2c2FmtThreshold);
      break;
    default:
      CHECK(false, "Interrupt from unexpected peripheral triggered");
  }

  status_t ret = i2c_device_emulate(i2c_idx, i2c_irq_id);

  // Acknowledge IRQ and return
  CHECK_DIF_OK(dif_i2c_irq_acknowledge(&i2cs[i2c_idx], i2c_irq_id));
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kHart, plic_irq_id));
  return ret;
}

bool test_main(void) {
  memset(&devices, 0u, sizeof(devices));

  const uintptr_t kI2cBaseAddrs[3] = {TOP_EARLGREY_I2C0_BASE_ADDR,
                                      TOP_EARLGREY_I2C1_BASE_ADDR,
                                      TOP_EARLGREY_I2C2_BASE_ADDR};

  for (size_t i = 0; i < ARRAYSIZE(i2cs); i++) {
    mmio_region_t i2c_region;
    i2c_region = mmio_region_from_addr(kI2cBaseAddrs[i]);
    CHECK_DIF_OK(dif_i2c_init(i2c_region, &i2cs[i]));
    CHECK_STATUS_OK(i2c_setup(&i2cs[i]));
  }

  mmio_region_t plic_region =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_region, &plic));

  rv_plic_testutils_irq_range_enable(&plic, kHart,
                                     kTopEarlgreyPlicIrqIdI2c0FmtThreshold,
                                     kTopEarlgreyPlicIrqIdI2c2HostTimeout);

  for (size_t i = 0; i < ARRAYSIZE(i2cs); i++) {
    CHECK_DIF_OK(dif_i2c_irq_set_enabled(&i2cs[i], kDifI2cIrqAcqThreshold,
                                         kDifToggleEnabled));
  }

  quit = false;
  isr_status = OK_STATUS();

  irq_external_ctrl(true);
  LOG_INFO("SYNC: Device Ready");

  ATOMIC_WAIT_FOR_INTERRUPT(quit == true || !status_ok(isr_status));

  return status_ok(isr_status);
}
