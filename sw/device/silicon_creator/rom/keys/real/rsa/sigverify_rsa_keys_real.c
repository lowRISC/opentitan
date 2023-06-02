// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/dev_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/dev_key_1_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/prod_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/prod_key_1_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/prod_key_2_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/test_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/real/rsa/test_key_1_rsa_3072_exp_f4.h"
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
                .key = TEST_KEY_0_RSA_3072_EXP_F4,
                .key_type = kSigverifyKeyTypeTest,
            },
    },
    {
        .entry =
            {
                .key = TEST_KEY_1_RSA_3072_EXP_F4,
                .key_type = kSigverifyKeyTypeTest,
            },
    },
    {
        .entry =
            {
                .key = DEV_KEY_0_RSA_3072_EXP_F4,
                .key_type = kSigverifyKeyTypeDev,
            },
    },
    {
        .entry =
            {
                .key = DEV_KEY_1_RSA_3072_EXP_F4,
                .key_type = kSigverifyKeyTypeDev,
            },
    },
    {
        .entry =
            {
                .key = PROD_KEY_0_RSA_3072_EXP_F4,
                .key_type = kSigverifyKeyTypeProd,
            },
    },
    {
        .entry =
            {
                .key = PROD_KEY_1_RSA_3072_EXP_F4,
                .key_type = kSigverifyKeyTypeProd,
            },
    },
    {
        .entry =
            {
                .key = PROD_KEY_2_RSA_3072_EXP_F4,
                .key_type = kSigverifyKeyTypeProd,
            },
    },
};

static_assert(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN_SIZE >=
                  kSigverifyRsaKeysCnt_,
              "CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN OTP item must be at least "
              "`kSigVerifyRsaKeysCnt` bytes.");
