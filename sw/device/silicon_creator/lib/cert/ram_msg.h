// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_RAM_MSG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_RAM_MSG_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

enum {
  kDiceCertGenRequest = 0x7d14bc2d,
  kDiceCertGenIds = 0x998bee21,
  kDiceCertGenResponse = 0x4f20f9a9,
};

/**
 * Header for DICE certificate generation messages.
 */
typedef struct dice_cert_gen_hdr {
  /* Message type identifier. */
  uint32_t type;
  /* Version of the message format. */
  uint32_t version;
} dice_cert_gen_hdr_t;

/**
 * Request message to trigger on-demand DICE certificate regenerate.
 *
 * Under On-Demand mode, OwnerSw requests generation by putting a
 * `kDiceCertGenRequest` message and then rebooting to ROM_EXT.
 *
 * Direction: Request from OwnerSw to ROM_EXT.
 */
typedef struct dice_cert_gen_req {
  /* Message header. Must be `kDiceCertGenRequest - v0`. */
  dice_cert_gen_hdr_t hdr;
} dice_cert_gen_req_t;

/**
 * Informational ID payload provided when certificate generation is skipped.
 *
 * When certificate generation is skipped, ROM_EXT provides the 64-bit key pair
 * IDs. OwnerSw can verify these IDs against cached certificates to determine
 * whether to trigger a generation.
 *
 * Direction: Response from ROM_EXT to OwnerSw.
 */
typedef struct dice_cert_gen_ids {
  /* Message header. Must be `kDiceCertGenIds - v0`. */
  dice_cert_gen_hdr_t hdr;
  /* Unique identifier of the CDI_0 certificate. Cached cert is valid for this
   * boot if the ID matches. */
  uint32_t mldsa_cdi0_id[2];
  /* Unique identifier of the CDI_1 certificate. Cached cert is valid for this
   * boot if the ID matches. */
  uint32_t mldsa_cdi1_id[2];
} dice_cert_gen_ids_t;

/**
 * Full handover response payload containing generated certificates.
 * Inherits the `dice_cert_gen_ids_t` struct.
 *
 * When cert generation conditions meet, ROM_EXT responds with the keypair IDs,
 * certificate buffer pointers and their lengths, then sets crc32 to protect the
 * integrity of these pointers. The keypair ID serves as a compact
 * representation of the CDI_0/1 key pair; matching IDs means that the key pairs
 * are identical.
 *
 * IMPORTANT - Relocation Responsibility:
 *   These returned buffer addresses may be placed in any arbitrary region
 *   within RAM (except the first 8 KB and last 8KB regions of the RAM).
 *   It is OwnerSw's responsibility to move them to their expected places at
 *   the beginning of the boot before OwnerSw overwrites those RAM regions.
 *
 * Direction: Response from ROM_EXT to OwnerSw.
 */
typedef struct dice_cert_gen_res {
  /* Message header. Must be `kDiceCertGenResponse - v0`. */
  dice_cert_gen_hdr_t hdr;
  /* Unique identifier of the CDI_0 certificate provided below. */
  uint32_t mldsa_cdi0_id[2];
  /* Unique identifier of the CDI_1 certificate provided below. */
  uint32_t mldsa_cdi1_id[2];

  /* Pointer to the CDI_0 certificate buffer in RAM. */
  uint32_t mldsa_cdi0_cert;
  /* Length of the CDI_0 certificate in bytes. */
  uint32_t mldsa_cdi0_cert_len;
  /* Pointer to the CDI_1 certificate buffer in RAM. */
  uint32_t mldsa_cdi1_cert;
  /* Length of the CDI_1 certificate in bytes. */
  uint32_t mldsa_cdi1_cert_len;
  /* Pointer to the UDS public key buffer in RAM. */
  uint32_t mldsa_uds_pub;
  /* Length of the UDS public key in bytes. */
  uint32_t mldsa_uds_pub_len;
  /* Reserved for future expansion. */
  uint32_t reserved[8];
  /* CRC32 checksum covering the preceding fields (essential to ensure pointer
   * integrity). */
  uint32_t crc32;
} dice_cert_gen_res_t;

typedef union dice_cert_gen_msg {
  dice_cert_gen_hdr_t hdr;
  dice_cert_gen_req_t req;
  dice_cert_gen_ids_t ids;
  dice_cert_gen_res_t res;
} dice_cert_gen_msg_t;

OT_ASSERT_SIZE(dice_cert_gen_hdr_t, 8);
OT_ASSERT_SIZE(dice_cert_gen_req_t, 8);
OT_ASSERT_SIZE(dice_cert_gen_ids_t, 24);
OT_ASSERT_SIZE(dice_cert_gen_res_t, 84);
OT_ASSERT_SIZE(dice_cert_gen_msg_t, 84);

OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_hdr_t, type, 0);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_hdr_t, version, 4);

OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_req_t, hdr, 0);

OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_ids_t, hdr, 0);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_ids_t, mldsa_cdi0_id, 8);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_ids_t, mldsa_cdi1_id, 16);

OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, hdr, 0);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, mldsa_cdi0_id, 8);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, mldsa_cdi1_id, 16);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, mldsa_cdi0_cert, 24);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, mldsa_cdi0_cert_len, 28);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, mldsa_cdi1_cert, 32);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, mldsa_cdi1_cert_len, 36);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, mldsa_uds_pub, 40);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, mldsa_uds_pub_len, 44);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, reserved, 48);
OT_ASSERT_MEMBER_OFFSET(dice_cert_gen_res_t, crc32, 80);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_RAM_MSG_H_
