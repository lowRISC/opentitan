// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_DICE_CDI_0_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_DICE_CDI_0_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"

enum {
  kCdi0CertStaticCriticalSizeBytes = 1024,
};

// The dice chain information that the immutable ROM_EXT will pass to the
// mutable ROM_EXT.
typedef struct {
  hmac_digest_t uds_pubkey_id;
  hmac_digest_t cdi_0_pubkey_id;
  uint32_t cert_size;
  uint8_t cert_data[kCdi0CertStaticCriticalSizeBytes];
} static_dice_cdi_0_t;

OT_ASSERT_MEMBER_OFFSET(static_dice_cdi_0_t, uds_pubkey_id, 0);
OT_ASSERT_MEMBER_OFFSET(static_dice_cdi_0_t, cdi_0_pubkey_id, 32);
OT_ASSERT_MEMBER_OFFSET(static_dice_cdi_0_t, cert_size, 64);
OT_ASSERT_MEMBER_OFFSET(static_dice_cdi_0_t, cert_data, 68);
OT_ASSERT_SIZE(static_dice_cdi_0_t, 1092);

extern static_dice_cdi_0_t static_dice_cdi_0;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_DICE_CDI_0_H_
