// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_STATUS_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_STATUS_H_

#define UJSON_CHECK_DIF_OK(dif_call) \
  do {                               \
    if (dif_call != kDifOk) {        \
      return ABORTED();              \
    }                                \
  } while (false)

#define UJSON_CHECK_STATUS_OK(status) \
  do {                                \
    if (status.value != 0) {          \
      return ABORTED();               \
    }                                 \
  } while (false)

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_STATUS_H_
