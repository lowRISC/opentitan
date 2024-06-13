// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"

// `extern` declarations for `inline` functions in the header.
extern uint32_t sigverify_ecdsa_p256_key_id_get(
    const ecdsa_p256_public_key_t *pub_key);
