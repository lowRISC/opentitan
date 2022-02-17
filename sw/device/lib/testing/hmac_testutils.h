// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_HMAC_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_HMAC_TESTUTILS_H_

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_hmac.h"

/**
 * Read and compare the length of the message in the HMAC engine to the length
 * of the message sent in bits.
 */
void hmac_testutils_check_message_length(const dif_hmac_t *hmac,
                                         uint64_t expected_sent_bits);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_HMAC_TESTUTILS_H_
