// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/status.h"

#include "sw/device/lib/base/hardened_status.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

crypto_status_t crypto_status_interpret(status_t status) {
  HARDENED_TRY(status);
  return status;
}
