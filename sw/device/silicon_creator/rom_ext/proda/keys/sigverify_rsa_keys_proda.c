// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/rom_ext/proda/keys/earlgrey_z1_proda_1.h"
#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"

/**
 * Number of RSA public keys.
 */
enum {
  kSigverifyRsaKeysCnt_ = 1,
};
const size_t kSigverifyRsaKeysCnt = kSigverifyRsaKeysCnt_;

/**
 * Step size to use when checking RSA public keys.
 *
 * This must be coprime with and less than `kSigverifyNumRsaKeys`.
 * Note: Step size is not applicable when `kSigverifyNumRsaKeys` is 1.
 */
const size_t kSigverifyRsaKeysStep = 1;

/**
 * Fake public keys for signature verification in tests.
 *
 * Please see sw/device/silicon_creator/rom/keys/README.md for more
 * details.
 */
const sigverify_rom_ext_key_t kSigverifyRsaKeys[kSigverifyRsaKeysCnt_] = {
    {
        .key = EARLGREY_Z1_PRODA_1,
        .key_type = kSigverifyKeyTypeFirmwareProd,
    },
};
