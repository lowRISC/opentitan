// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/aes_testutils.h"

extern bool aes_testutils_get_status(dif_aes_t *aes, dif_aes_status_t flag);

extern void aes_testutils_wait_for_status(dif_aes_t *aes, dif_aes_status_t flag,
                                          bool value, uint32_t timeout_usec);
