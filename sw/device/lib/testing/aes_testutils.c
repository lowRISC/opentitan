// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/aes_testutils.h"

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern bool aes_testutils_get_status(dif_aes_t *aes, dif_aes_status_t flag);
