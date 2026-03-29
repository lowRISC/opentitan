// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/entropy_src.h"

#include <stdbool.h>

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', 't', 's')

otcrypto_status_t otcrypto_entropy_init(void) {
  HARDENED_TRY(entropy_complex_init());
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_entropy_check(void) {
  HARDENED_TRY(entropy_complex_check());
  return OTCRYPTO_OK;
}
