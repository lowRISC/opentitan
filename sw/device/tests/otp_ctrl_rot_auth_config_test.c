// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/manuf/lib/otp_img_types.h"
#include "sw/device/silicon_creator/manuf/lib/util.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

enum {
  kValidAstCfgOtpAddrLow = OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_OFFSET,
  kInvalidAstCfgOtpAddrHigh =
      kValidAstCfgOtpAddrLow + OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_SIZE,
};

// Partition ROT_CREATOR_AUTH_CODESIGN values
static const uint32_t kRotCreatorAuthCodesignEcdsaKeyType0Value = 0x43a839ad;
static const uint32_t kRotCreatorAuthCodesignEcdsaKey0Value[] = {
    0x8aa047bb, 0x51ea3f68, 0x661f5601, 0x91e7b09d, 0x6444702e, 0xde569ca5,
    0x74cbb86e, 0xc48c6962, 0xb6cbbeba, 0x48650d82, 0x4f9b1f08, 0x1ad8bc61,
    0x5f1f81f7, 0x3bfb4400, 0x14cd7857, 0x112eb536,
};
static const uint32_t kRotCreatorAuthCodesignEcdsaKeyType1Value = 0x43a839ad;
static const uint32_t kRotCreatorAuthCodesignEcdsaKey1Value[] = {
    0xc436fc3d, 0x4adc632b, 0x1cd5c4d8, 0x2964ca99, 0xaf46824f, 0xd29e7624,
    0x489446e9, 0x2a7f529f, 0xd6aaf46d, 0x38cf545a, 0x84363edc, 0xc73d4c13,
    0xf2479b3c, 0x43d70b86, 0xcf8ca3f4, 0x8f522f2b,
};
static const uint32_t kRotCreatorAuthCodesignEcdsaKeyType2Value = 0x43a839ad;
static const uint32_t kRotCreatorAuthCodesignEcdsaKey2Value[] = {
    0xa7948feb, 0x08384089, 0x46603509, 0xda8a1db4, 0x3574ccc3, 0x27348cb6,
    0xd7ff3af1, 0xbde6d117, 0x25136e20, 0xbec154fb, 0x1c3e5f45, 0x9c8001ba,
    0x58bb55f8, 0x4c421e8f, 0xeaec69f0, 0x1295b177,
};
static const uint32_t kRotCreatorAuthCodesignEcdsaKeyType3Value = 0x3ff0c819;
static const uint32_t kRotCreatorAuthCodesignEcdsaKey3Value[] = {
    0x473d006d, 0xcacaa3d3, 0x3bbdf26a, 0x132eff0b, 0x9f8da3a3, 0xbabd1068,
    0xe2acf000, 0x3b4c161c, 0x960005ea, 0xde83bf38, 0xe7bdb33e, 0xf4d513f4,
    0x3806de08, 0xf53f530a, 0x4afd697a, 0x39dc0465,
};
static const uint32_t kRotCreatorAuthCodesignBlockSha2256HashValue[] = {
    0x9158ed20, 0xc9121526, 0xb8ab4f00, 0x3fc85d46,
    0x1d78ed0e, 0x546e780e, 0x56aa3798, 0x8f8e8382,
};

// Partition ROT_CREATOR_AUTH_STATE values
static const uint32_t kRotCreatorAuthStateEcdsaKey0Value = 0xe8a16781;
static const uint32_t kRotCreatorAuthStateEcdsaKey1Value = 0xe8a16781;
static const uint32_t kRotCreatorAuthStateEcdsaKey2Value = 0xe8a16781;
static const uint32_t kRotCreatorAuthStateEcdsaKey3Value = 0xe8a16781;

// Partition ROT_CREATOR_AUTH_CODESIGN
const size_t kOtpKvRotCreatorAuthCodesignSize = 9;
const otp_kv_t kOtpKvRotCreatorAuthCodesign[] = {
    {
        .type = kOptValTypeUint32Buff,
        .offset =
            OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE0_OFFSET,
        .num_values = 1,
        .value32 = &kRotCreatorAuthCodesignEcdsaKeyType0Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY0_OFFSET,
        .num_values = 16,
        .value32 = kRotCreatorAuthCodesignEcdsaKey0Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset =
            OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE1_OFFSET,
        .num_values = 1,
        .value32 = &kRotCreatorAuthCodesignEcdsaKeyType1Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY1_OFFSET,
        .num_values = 16,
        .value32 = kRotCreatorAuthCodesignEcdsaKey1Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset =
            OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE2_OFFSET,
        .num_values = 1,
        .value32 = &kRotCreatorAuthCodesignEcdsaKeyType2Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY2_OFFSET,
        .num_values = 16,
        .value32 = kRotCreatorAuthCodesignEcdsaKey2Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset =
            OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY_TYPE3_OFFSET,
        .num_values = 1,
        .value32 = &kRotCreatorAuthCodesignEcdsaKeyType3Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_ECDSA_KEY3_OFFSET,
        .num_values = 16,
        .value32 = kRotCreatorAuthCodesignEcdsaKey3Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROTCREATORAUTHCODESIGNBLOCKSHA2_256HASHOFFSET,
        .num_values = 8,
        .value32 = kRotCreatorAuthCodesignBlockSha2256HashValue,
    },
};

// Partition ROT_CREATOR_AUTH_STATE
const size_t kOtpKvRotCreatorAuthStateSize = 4;
const otp_kv_t kOtpKvRotCreatorAuthState[] = {
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_ECDSA_KEY0_OFFSET,
        .num_values = 1,
        .value32 = &kRotCreatorAuthStateEcdsaKey0Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_ECDSA_KEY1_OFFSET,
        .num_values = 1,
        .value32 = &kRotCreatorAuthStateEcdsaKey1Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_ECDSA_KEY2_OFFSET,
        .num_values = 1,
        .value32 = &kRotCreatorAuthStateEcdsaKey2Value,
    },
    {
        .type = kOptValTypeUint32Buff,
        .offset = OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_ECDSA_KEY3_OFFSET,
        .num_values = 1,
        .value32 = &kRotCreatorAuthStateEcdsaKey3Value,
    },
};

/**
 * Writes OTP values to target OTP `partition`.
 *
 * The `kv` array is preferrably generated using the build infrastructure. See
 * individualize_preop.c and its build target for an example.
 *
 * @param otp OTP Controller instance.
 * @param partition Target OTP partition.
 * @param kv OTP Array of OTP key values. See `otp_kv_t` documentation for more
 * details.
 * @param len Length of the `kv` array.
 * @return OT_WARN_UNUSED_RESULT
 */
OT_WARN_UNUSED_RESULT
static status_t otp_img_write(const dif_otp_ctrl_t *otp,
                              dif_otp_ctrl_partition_t partition,
                              const otp_kv_t *kv, size_t len) {
  for (size_t i = 0; i < len; ++i) {
    // We purposely skip the provisioning of the flash data region default
    // configuration as it must be enabled only after the OTP SECRET1
    // partition has been provisioned. Since OTP SECRET1 provisioning requires
    // the HW_CFG0 partition to be provisioned to use the CSRNG SW interface,
    // there is a delicate order of operations in which this field is
    // provisioned. Therefore we require explicit provisioning of this field
    // immediately before the transport image is loaded, after all other
    // provisioning is complete.
    //
    // Additionally, we skip the provisioning of the AST configuration data, as
    // this should already be written to a flash info page. We will pull the
    // data directly from there.
    if (kv[i].offset ==
            OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET ||
        (kv[i].offset >= kValidAstCfgOtpAddrLow &&
         kv[i].offset < kInvalidAstCfgOtpAddrHigh)) {
      continue;
    }
    uint32_t offset;
    TRY(dif_otp_ctrl_relative_address(partition, kv[i].offset, &offset));
    switch (kv[i].type) {
      case kOptValTypeUint32Buff:
        TRY(otp_ctrl_testutils_dai_write32(otp, partition, offset,
                                           kv[i].value32, kv[i].num_values));
        break;
      case kOptValTypeUint64Buff:
        TRY(otp_ctrl_testutils_dai_write64(otp, partition, offset,
                                           kv[i].value64, kv[i].num_values));
        break;
      case kOptValTypeUint64Rnd:
        return UNIMPLEMENTED();
      default:
        return INTERNAL();
    }
  }
  return OK_STATUS();
}

/**
 * Computes a SHA256 digest of an OTP partition and uses the least significant
 * 64-bits of the digest to additionally lock the partition.
 *
 * Note: only {Creator,Owner}SwCfg partitions and the VendorTest partition may
 * be locked in this manner. All other partitions are locked via hardware.
 *
 * @param otp OTP Controller instance.
 * @param partition Target OTP partition.
 * @return OT_WARN_UNUSED_RESULT
 */
OT_WARN_UNUSED_RESULT
static status_t lock_otp_partition(const dif_otp_ctrl_t *otp_ctrl,
                                   dif_otp_ctrl_partition_t partition) {
  // Compute SHA256 of the OTP partition.
  uint32_t digest[kSha256DigestWords];
  otcrypto_word32_buf_t otp_partition_digest = {
      .len = ARRAYSIZE(digest),
      .data = digest,
  };
  TRY(manuf_util_hash_otp_partition(otp_ctrl, partition, otp_partition_digest));

  // Get the least significant 64 bits of the digest. We will use this as the
  // digest to lock the OTP partition. The complete digest will be used in the
  // attestation key / certificate generation. Note: cryptolib generates the
  // digest in big-endian format so we must rearrange the bytes.
  uint64_t partition_digest_lowest_64bits = __builtin_bswap32(digest[6]);
  partition_digest_lowest_64bits =
      (partition_digest_lowest_64bits << 32) | __builtin_bswap32(digest[7]);

  TRY(otp_ctrl_testutils_lock_partition(
      otp_ctrl, partition, /*digest=*/partition_digest_lowest_64bits));

  return OK_STATUS();
}

static status_t manuf_individualize_device_rot_creator_auth_codesign(
    const dif_otp_ctrl_t *otp_ctrl) {
  TRY(otp_img_write(otp_ctrl, kDifOtpCtrlPartitionRotCreatorAuthCodesign,
                    kOtpKvRotCreatorAuthCodesign,
                    kOtpKvRotCreatorAuthCodesignSize));
  if (kDeviceType != kDeviceSimDV) {
    TRY(lock_otp_partition(otp_ctrl,
                           kDifOtpCtrlPartitionRotCreatorAuthCodesign));
  }
  return OK_STATUS();
}

static status_t manuf_individualize_device_rot_creator_auth_state(
    const dif_otp_ctrl_t *otp_ctrl) {
  TRY(otp_img_write(otp_ctrl, kDifOtpCtrlPartitionRotCreatorAuthState,
                    kOtpKvRotCreatorAuthState, kOtpKvRotCreatorAuthStateSize));
  TRY(lock_otp_partition(otp_ctrl, kDifOtpCtrlPartitionRotCreatorAuthState));
  return OK_STATUS();
}

bool test_main(void) {
  static dif_otp_ctrl_t otp_ctrl;
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_STATUS_OK(
      manuf_individualize_device_rot_creator_auth_codesign(&otp_ctrl));
  if (kDeviceType != kDeviceSimDV) {
    CHECK_STATUS_OK(
        manuf_individualize_device_rot_creator_auth_state(&otp_ctrl));
  }
  return true;
}
