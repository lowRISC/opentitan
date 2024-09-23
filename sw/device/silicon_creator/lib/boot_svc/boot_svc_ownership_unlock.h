// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_UNLOCK_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_UNLOCK_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/nonce.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  // ASCII: ANY
  kBootSvcUnlockAny = 0x00594e41,
  // ASCII: ENDO
  kBootSvcUnlockEndorsed = 0x4f444e45,
  // ASCII: UPD
  kBootSvcUnlockUpdate = 0x00445055,
  // ASCII: ABRT
  kBootSvcUnlockAbort = 0x54524241,

  /** Ownership unlock request: `UNLK`. */
  kBootSvcOwnershipUnlockReqType = 0x4b4c4e55,
  /** Ownership unlock response: `KLNU`. */
  kBootSvcOwnershipUnlockResType = 0x554e4c4b,
};

/**
 * An ownership unlock request.
 */
typedef struct boot_svc_ownership_unlock_req {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Unlock mode: Any, Endorsed, Update or Abort.
   */
  uint32_t unlock_mode;
  /**
   * The 64-bit ID subfield of the full 256-bit device ID.
   */
  uint32_t din[2];
  /**
   * Reserved for future use.
   */
  uint32_t reserved[8];
  /**
   * The current ownership nonce.
   */
  nonce_t nonce;
  /**
   * The public key of the next owner (for endorsed mode).
   */
  owner_key_t next_owner_key;
  /**
   * Signature over [unlock_mode..next_owner_key]
   */
  owner_signature_t signature;

} boot_svc_ownership_unlock_req_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_req_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_req_t, unlock_mode,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_req_t, din,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 4);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_req_t, reserved,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 12);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_req_t, nonce,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 44);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_req_t, next_owner_key,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 52);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_req_t, signature,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 148);
OT_ASSERT_SIZE(boot_svc_ownership_unlock_req_t, 256);

/**
 * An ownership unlock response.
 */
typedef struct boot_svc_ownership_unlock_res {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Response status from the ROM_EXT.
   */
  rom_error_t status;
} boot_svc_ownership_unlock_res_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_res_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_unlock_res_t, status,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_SIZE(boot_svc_ownership_unlock_res_t, 48);

/**
 * Initialize an ownership unlock request.
 *
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_ownership_unlock_req_init(uint32_t unlock_mode, nonce_t nonce,
                                        const owner_key_t *next_owner_key,
                                        const owner_signature_t *signature,
                                        boot_svc_ownership_unlock_req_t *msg);

/**
 * Initialize an ownership unlock response.
 *
 * @param status Reponse from the ROM_EXT after receiving the request.
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_ownership_unlock_res_init(rom_error_t status,
                                        boot_svc_ownership_unlock_res_t *msg);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_UNLOCK_H_
