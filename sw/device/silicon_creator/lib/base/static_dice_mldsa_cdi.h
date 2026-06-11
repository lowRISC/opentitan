// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_DICE_MLDSA_CDI_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_DICE_MLDSA_CDI_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

// The post-quantum DICE chain information passed from imm_section to
// ROM_EXT, and from ROM_EXT to the Owner image.
typedef struct {
  uint8_t uds_pub[2592];
  uint32_t uds_pub_size;
  uint8_t cdi_0_cert[8192];
  uint32_t cdi_0_cert_size;
  uint8_t cdi_1_cert[8192];
  uint32_t cdi_1_cert_size;
} static_dice_mldsa_cdi_t;

OT_ASSERT_MEMBER_OFFSET(static_dice_mldsa_cdi_t, uds_pub, 0);
OT_ASSERT_MEMBER_OFFSET(static_dice_mldsa_cdi_t, uds_pub_size, 2592);
OT_ASSERT_MEMBER_OFFSET(static_dice_mldsa_cdi_t, cdi_0_cert, 2596);
OT_ASSERT_MEMBER_OFFSET(static_dice_mldsa_cdi_t, cdi_0_cert_size, 10788);
OT_ASSERT_MEMBER_OFFSET(static_dice_mldsa_cdi_t, cdi_1_cert, 10792);
OT_ASSERT_MEMBER_OFFSET(static_dice_mldsa_cdi_t, cdi_1_cert_size, 18984);
OT_ASSERT_SIZE(static_dice_mldsa_cdi_t, 18988);

extern static_dice_mldsa_cdi_t static_dice_mldsa_cdi;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_STATIC_DICE_MLDSA_CDI_H_
