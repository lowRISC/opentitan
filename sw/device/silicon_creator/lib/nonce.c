// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/nonce.h"

#include "sw/device/silicon_creator/lib/drivers/rnd.h"

void nonce_new(nonce_t *nonce) {
  nonce->value[0] = rnd_uint32();
  nonce->value[1] = rnd_uint32();
}

extern bool nonce_equal(const nonce_t *a, const nonce_t *b);
