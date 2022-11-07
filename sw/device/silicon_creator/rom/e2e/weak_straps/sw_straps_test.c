// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_gpio_t gpio;
static dif_pinmux_t pinmux;
OTTF_DEFINE_TEST_CONFIG();

status_t strap_test(dif_pinmux_t *pinmux, dif_gpio_t *gpio) {
  uint32_t strap = pinmux_testutils_read_straps(pinmux, gpio);
  LOG_INFO("sw_strap=%d", strap);
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

  pinmux_testutils_init(&pinmux);
  status_t s = strap_test(&pinmux, &gpio);
  if (status_err(s)) {
    LOG_ERROR("error = %r", s);
    return false;
  }
  return true;
}
