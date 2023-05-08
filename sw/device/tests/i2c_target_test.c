// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/testing/json/i2c_target.h"

#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_pinmux_t pinmux;
static dif_i2c_t i2c;

enum {
  kTestTimeout = 1000000,     // 1 second
  kTransactionDelay = 10000,  // 10 ms
};

static status_t configure_device_address(ujson_t *uj, dif_i2c_t *i2c) {
  i2c_target_address_t address;
  TRY(ujson_deserialize_i2c_target_address_t(uj, &address));
  TRY(dif_i2c_host_set_enabled(i2c, kDifToggleDisabled));
  TRY(dif_i2c_device_set_enabled(i2c, kDifToggleDisabled));
  dif_i2c_id_t id0 = {
      .mask = address.mask0,
      .address = address.id0,
  };
  dif_i2c_id_t id1 = {
      .mask = address.mask1,
      .address = address.id1,
  };
  TRY(dif_i2c_set_device_id(i2c, &id0, &id1));
  TRY(dif_i2c_device_set_enabled(i2c, kDifToggleEnabled));
  return RESP_OK_STATUS(uj);
}

static status_t wait_for_acq_fifo(dif_i2c_t *i2c, uint8_t at_least,
                                  const ibex_timeout_t *deadline) {
  uint8_t acq_fifo_lvl;
  while (!ibex_timeout_check(deadline)) {
    if (dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl) ==
            kDifOk &&
        acq_fifo_lvl >= at_least) {
      return OK_STATUS();
    }
  }
  return DEADLINE_EXCEEDED();
}

static status_t recv_write_transaction(dif_i2c_t *i2c, i2c_transaction_t *txn,
                                       uint32_t micros, uint32_t delay_micros) {
  ibex_timeout_t deadline = ibex_timeout_init(micros);
  uint8_t byte;
  dif_i2c_signal_t signal;

  // Address phase.
  TRY(wait_for_acq_fifo(i2c, 1, &deadline));
  TRY(dif_i2c_acquire_byte(i2c, &byte, &signal));
  TRY_CHECK(signal == kDifI2cSignalStart);
  txn->address = byte >> 1;

  // Data phase.
  while (true) {
    if (txn->length % 64 == 0 && delay_micros) {
      busy_spin_micros(delay_micros);
    }
    TRY(wait_for_acq_fifo(i2c, 1, &deadline));
    TRY(dif_i2c_acquire_byte(i2c, &byte, &signal));
    if (signal != kDifI2cSignalNone) {
      break;
    }
    txn->data[txn->length++] = byte;
  }

  // End of transaction.
  switch (signal) {
    case kDifI2cSignalStop:
      return OK_STATUS(false);
    case kDifI2cSignalRepeat:
      txn->continuation = byte;
      return OK_STATUS(true);
    default:
      return INTERNAL();
  }
}

static status_t read_transaction(ujson_t *uj, dif_i2c_t *i2c) {
  i2c_transaction_t txn;
  TRY(ujson_deserialize_i2c_transaction_t(uj, &txn));
  TRY(i2c_testutils_target_read(i2c, txn.length, txn.data));
  ibex_timeout_t deadline = ibex_timeout_init(kTestTimeout);
  TRY(wait_for_acq_fifo(i2c, 2, &deadline));
  i2c_rx_result_t result = {0, 0};
  TRY(i2c_testutils_target_check_read(i2c, &result.address,
                                      &result.continuation));
  return RESP_OK(ujson_serialize_i2c_rx_result_t, uj, &result);
}

static status_t write_transaction(ujson_t *uj, dif_i2c_t *i2c,
                                  uint32_t delay_micros) {
  i2c_transaction_t txn = {0};
  TRY(recv_write_transaction(i2c, &txn, kTestTimeout, delay_micros));
  return RESP_OK(ujson_serialize_i2c_transaction_t, uj, &txn);
}

static status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    switch (command) {
      case kTestCommandI2cTargetAddress:
        RESP_ERR(uj, configure_device_address(uj, &i2c));
        break;
      case kTestCommandI2cReadTransaction:
        RESP_ERR(uj, read_transaction(uj, &i2c));
        break;
      case kTestCommandI2cWriteTransaction:
        RESP_ERR(uj, write_transaction(uj, &i2c, 0));
        break;
      case kTestCommandI2cWriteTransactionSlow:
        // We'll insert a 10ms delay every 64 bytes, which is a huge delay
        // at 100 KHz, forcing the peripheral to stretch the clock.
        RESP_ERR(uj, write_transaction(uj, &i2c, kTransactionDelay));
        break;
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }
  // We should never reach here.
  return INTERNAL();
}

static status_t test_init(void) {
  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux));

  TRY(i2c_testutils_connect_i2c_to_pinmux_pins(&pinmux, 0));

  TRY(i2c_testutils_set_speed(&i2c, kDifI2cSpeedStandard));
  TRY(dif_i2c_device_set_enabled(&i2c, kDifToggleEnabled));
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(test_init());
  status_t status;
  ujson_t uj = ujson_ottf_console();
  status = command_processor(&uj);
  LOG_INFO("status = %r", status);
  return status_ok(status);
}
