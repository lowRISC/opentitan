// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_HISTORY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_HISTORY_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /** Ownership history request: `HIST`. */
  kBootSvcOwnershipHistoryReqType = 0x54534948,
  /** Ownership history response: `TSIH`. */
  kBootSvcOwnershipHistoryResType = 0x48495354,
};

/**
 * An Ownership History request.
 */
typedef struct boot_svc_ownership_history_req {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
} boot_svc_ownership_history_req_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_history_req_t, header, 0);
OT_ASSERT_SIZE(boot_svc_ownership_history_req_t, CHIP_BOOT_SVC_MSG_HEADER_SIZE);

/**
 * An Ownership History response.
 */
typedef struct boot_svc_ownership_history_res {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * Response status from the ROM_EXT.
   */
  uint32_t status;
  /**
   * Digest of all prior owner keys.
   */
  uint32_t history_digest[8];
} boot_svc_ownership_history_res_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_history_res_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_history_res_t, status,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_MEMBER_OFFSET(boot_svc_ownership_history_res_t, history_digest,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE + 4);
OT_ASSERT_SIZE(boot_svc_ownership_history_res_t, 80);

/**
 * Initialize an ownership history request.
 *
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_ownership_history_req_init(boot_svc_ownership_history_req_t *msg);

/**
 * Initialize an ownership history response.
 *
 * @param status Reponse from the ROM_EXT after receiving the request.
 * @param history_digest Digest of all prior owner keys.
 *        The digest is computed each time there is an ownership transfer.
 *        The new digest is SHA256(previous_digest || new_owner_key).
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_ownership_history_res_init(rom_error_t status,
                                         const uint32_t *history_digest,
                                         boot_svc_ownership_history_res_t *msg);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_OWNERSHIP_HISTORY_H_
