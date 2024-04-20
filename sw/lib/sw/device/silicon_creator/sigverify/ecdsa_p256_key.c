// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/lib/sw/device/silicon_creator/sigverify/ecdsa_p256_key.h"

// `extern` declarations for `inline` functions in the header.
extern uint32_t sigverify_ecdsa_p256_key_id_get(
    const sigverify_ecdsa_p256_buffer_t *pub_key);
