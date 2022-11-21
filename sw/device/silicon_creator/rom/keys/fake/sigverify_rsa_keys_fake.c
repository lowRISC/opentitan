// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/rom/keys/fake/dev_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/fake/prod_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/keys/fake/test_key_0_rsa_3072_exp_f4.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_ptrs.h"

#include "otp_ctrl_regs.h"

/**
 * Fake public keys for signature verification in tests.
 *
 * Please see sw/device/silicon_creator/rom/keys/README.md for more
 * details.
 */
const sigverify_rom_key_t kSigverifyRsaKeys[kSigverifyRsaKeysCnt] = {
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
                  kSigverifyRsaKeysCnt,
              "CREATOR_SW_CFG_KEY_IS_VALID OTP item must be at least "
              "`kSigVerifyNumKeysFake` bytes.");

const sigverify_rom_key_t *sigverify_rsa_keys_get(void) {
  return kSigverifyRsaKeys;
}

size_t sigverify_rsa_keys_cnt_get(void) { return kSigverifyRsaKeysCnt; }

size_t sigverify_rsa_keys_step_get(void) { return kSigverifyRsaKeysStep; }
