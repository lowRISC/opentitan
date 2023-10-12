// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/util.h"

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

static_assert(
    OTP_CTRL_PARAM_VENDOR_TEST_SIZE % sizeof(uint32_t) == 0,
    "OTP Vendor Test partition should be an integer multiple of 32-bit words.");

status_t manuf_util_hash_lc_transition_token(const uint32_t *raw_token,
                                             size_t token_size_bytes,
                                             uint64_t *hashed_token) {
  crypto_const_byte_buf_t input = {
      .data = (unsigned char *)raw_token,
      .len = token_size_bytes,
  };
  crypto_const_byte_buf_t function_name_string = {
      .data = (unsigned char *)"",
      .len = 0,
  };
  crypto_const_byte_buf_t customization_string = {
      .data = (unsigned char *)"LC_CTRL",
      .len = 7,
  };

  // Create a temporary uint32_t buffer and copy the result from there to the
  // uint64_t buffer.
  // TODO(#16556): this is a workaround to avoid violating strict-aliasing; if
  // we pass -fno-strict-aliasing, then we can cast `hashed_token` to `uint32_t
  // *` instead.
  size_t token_num_words = token_size_bytes / sizeof(uint32_t);
  if (token_size_bytes % sizeof(uint32_t) != 0) {
    token_num_words++;
  }
  uint32_t token_data[token_num_words];
  memset(token_data, 0, sizeof(token_data));
  crypto_word32_buf_t output = {
      .data = token_data,
      .len = token_num_words,
  };

  TRY(otcrypto_xof_cshake(input, kXofCshakeModeCshake128, function_name_string,
                          customization_string, token_size_bytes, &output));
  memcpy(hashed_token, token_data, sizeof(token_data));

  return OK_STATUS();
}

status_t manuf_util_hash_otp_partition(const dif_otp_ctrl_t *otp_ctrl,
                                       dif_otp_ctrl_partition_t partition,
                                       crypto_word32_buf_t *output) {
  if (otp_ctrl == NULL || output == NULL || output->len != kSha256DigestWords) {
    return INVALID_ARGUMENT();
  }

  switch (partition) {
    case kDifOtpCtrlPartitionVendorTest: {
      uint32_t vendor_test_32bit_array[OTP_CTRL_PARAM_VENDOR_TEST_SIZE /
                                       sizeof(uint32_t)];

      TRY(otp_ctrl_testutils_dai_read32_array(
          otp_ctrl, kDifOtpCtrlPartitionVendorTest, 0, vendor_test_32bit_array,
          OTP_CTRL_PARAM_VENDOR_TEST_SIZE / sizeof(uint32_t)));
      crypto_const_byte_buf_t input = {
          .data = (unsigned char *)vendor_test_32bit_array,
          .len = OTP_CTRL_PARAM_VENDOR_TEST_SIZE,
      };
      TRY(otcrypto_hash(input, kHashModeSha256, output));
    } break;
    case kDifOtpCtrlPartitionCreatorSwCfg: {
      crypto_const_byte_buf_t input = {
          .data = (unsigned char *)(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                                    OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET),
          .len = OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE,
      };
      TRY(otcrypto_hash(input, kHashModeSha256, output));
    } break;
    case kDifOtpCtrlPartitionOwnerSwCfg: {
      crypto_const_byte_buf_t input = {
          .data = (unsigned char *)(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                                    OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
                                    OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE),
          .len = OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE,
      };
      TRY(otcrypto_hash(input, kHashModeSha256, output));
    } break;
    default:
      return INVALID_ARGUMENT();
  }

  return OK_STATUS();
}
