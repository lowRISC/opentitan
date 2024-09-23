// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_ACTIVATE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_ACTIVATE_H_

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
  /** Ownership activate request: `ACTV`. */
  kBootSvcOwnershipActivateReqType = 0x56544341,
  /** Ownership activate response: `VTCA`. */
  kBootSvcOwnershipActivateResType = 0x41435456,
};

/**
 * An Ownership Activate request.
 */
typedef struct boot_svc_ownership_activate_req {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Which side of the flash is primary after activation.
   */
  uint32_t primary_bl0_slot;
  /**
   * The 64-bit DIN subfield of the full 256-bit device ID.
   */
  uint32_t din[2];
  /**
   * Erase previous owner's flash (hardened_bool_t).
   */
  uint32_t erase_previous;
  /**
   * Reserved for future use.
   */
  uint32_t reserved[31];
  /**
   * The current ownership nonce.
   */
  nonce_t nonce;
  /**
   * Signature over [primary_bl0_slot..nonce]
   */
  owner_signature_t signature;

} boot_svc_ownership_activate_req_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_req_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_req_t, primary_bl0_slot,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_req_t, din,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 4);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_req_t, erase_previous,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 12);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_req_t, reserved,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 16);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_req_t, nonce,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 140);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_req_t, signature,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 148);
OT_ASSERT_SIZE(boot_svc_ownership_activate_req_t, 256);

/**
 * An Ownership Activate response.
 */
typedef struct boot_svc_ownership_activate_res {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Response status from the ROM_EXT.
   */
  rom_error_t status;
} boot_svc_ownership_activate_res_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_res_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_activate_res_t, status,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_SIZE(boot_svc_ownership_activate_res_t, 48);

/**
 * Initialize an ownership activate request.
 *
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_ownership_activate_req_init(
    uint32_t primary_bl0_slot, uint32_t erase_previous, nonce_t nonce,
    const owner_signature_t *signature, boot_svc_ownership_activate_req_t *msg);

/**
 * Initialize an ownership activate response.
 *
 * @param status Reponse from the ROM_EXT after receiving the request.
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_ownership_activate_res_init(
    rom_error_t status, boot_svc_ownership_activate_res_t *msg);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_ACTIVATE_H_
