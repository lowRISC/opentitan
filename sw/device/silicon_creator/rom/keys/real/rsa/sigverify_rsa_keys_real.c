// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/earlgrey_a0_dev_0.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/earlgrey_a0_dev_1.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/earlgrey_a0_prod_0.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/earlgrey_a0_prod_1.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/earlgrey_a0_prod_2.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/earlgrey_a0_test_0.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/earlgrey_a0_test_1.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_rsa.h"

#include "otp_ctrl_regs.h"

/**
 * Number of RSA public keys.
 */
enum {
  kSigverifyRsaKeysCnt_ = 7,
};
const size_t kSigverifyRsaKeysCnt = kSigverifyRsaKeysCnt_;

/**
 * Step size to use when checking RSA public keys.
 *
 * This must be coprime with and less than `kSigverifyNumRsaKeys`.
 * Note: Step size is not applicable when `kSigverifyNumRsaKeys` is 1.
 */
const size_t kSigverifyRsaKeysStep = 5;

/**
 * Real public keys for signature verification.
 *
 * Please see sw/device/silicon_creator/rom/keys/README.md for more
 * details.
 */
const sigverify_rom_rsa_key_t kSigverifyRsaKeys[kSigverifyRsaKeysCnt_] = {
    {
        .entry =
            {
                .key = EARLGREY_A0_TEST_0,
                .key_type = kSigverifyKeyTypeTest,
            },
    },
    {
        .entry =
            {
                .key = EARLGREY_A0_TEST_1,
                .key_type = kSigverifyKeyTypeTest,
            },
    },
    {
        .entry =
            {
                .key = EARLGREY_A0_DEV_0,
                .key_type = kSigverifyKeyTypeDev,
            },
    },
    {
        .entry =
            {
                .key = EARLGREY_A0_DEV_1,
                .key_type = kSigverifyKeyTypeDev,
            },
    },
    {
        .entry =
            {
                .key = EARLGREY_A0_PROD_0,
                .key_type = kSigverifyKeyTypeProd,
            },
    },
    {
        .entry =
            {
                .key = EARLGREY_A0_PROD_1,
                .key_type = kSigverifyKeyTypeProd,
            },
    },
    {
        .entry =
            {
                .key = EARLGREY_A0_PROD_2,
                .key_type = kSigverifyKeyTypeProd,
            },
    },
};

static_assert(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN_SIZE >=
                  kSigverifyRsaKeysCnt_,
              "CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN OTP item must be at least "
              "`kSigVerifyRsaKeysCnt` bytes.");
