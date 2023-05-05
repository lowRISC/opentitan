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

status_t configure_device_address(ujson_t *uj, dif_i2c_t *i2c) {
  i2c_target_address_t address;
  TRY(ujson_deserialize_i2c_target_address_t(uj, &address));
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

status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    switch (command) {
      case kTestCommandI2cTargetAddress:
        RESP_ERR(uj, configure_device_address(uj, &i2c));
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

  TRY(dif_i2c_device_set_enabled(&i2c, kDifToggleEnabled));
  return OK_STATUS();
}

bool test_main(void) {
  status_t test_result;
  CHECK_STATUS_OK(test_init());

  ujson_t uj = ujson_ottf_console();
  status_t s = command_processor(&uj);
  LOG_INFO("status = %r", s);
  return status_ok(s);
}
