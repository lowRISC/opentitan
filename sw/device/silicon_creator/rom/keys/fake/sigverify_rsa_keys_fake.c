// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/rom/keys/fake/dev_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/fake/prod_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/fake/test_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/sigverify_keys.h"

#include "otp_ctrl_regs.h"

/**
 * Number of RSA public keys.
 */
enum {
  kSigverifyRsaKeysCnt_ = 3,
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
const sigverify_rom_key_t kSigverifyRsaKeys[kSigverifyRsaKeysCnt_] = {
    {
        .key = TEST_KEY_0_RSA_3072_EXP_F4,
        .key_type = kSigverifyKeyTypeTest,
    },
    {
        .key = DEV_KEY_0_RSA_3072_EXP_F4,
        .key_type = kSigverifyKeyTypeDev,
    },
    {
        .key = PROD_KEY_0_RSA_3072_EXP_F4,
        .key_type = kSigverifyKeyTypeProd,
    },
};

static_assert(OTP_CTRL_PARAM_CREATOR_SW_CFG_KEY_IS_VALID_SIZE >=
                  kSigverifyRsaKeysCnt_,
              "CREATOR_SW_CFG_KEY_IS_VALID OTP item must be at least "
              "`kSigVerifyNumKeysFake` bytes.");
